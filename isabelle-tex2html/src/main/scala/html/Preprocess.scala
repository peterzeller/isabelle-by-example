package html

import parser.Ast
import parser.Ast._

import scala.collection.mutable.ListBuffer

object Preprocess {

  val rules: List[Rule] = List(
    SimplifySeqs,
    RewriteCodeBlocks,
    Itemize
  )


  def rewrite(doc: Seq[Element]): Seq[Element] = {
    var d = doc
    for (rule <- rules) {
      d = rule.rewriteToplevel(d)
    }
    rewriteElems(d)
  }

  def rewriteElem(elem: Ast.Element): Ast.Element = {
    var e = elem
    for (rule <- rules) {
      e = rule.rewriteElement(e)
    }
    e match {
      case Text(text) => e
      case Block(tag, content) =>
        Block(tag, rewriteElem(content))
      case Command(tag, content) =>
        Command(tag, rewriteElem(content))
      case Elements(s) =>
        Elements(rewriteElems(s))
    }
  }

  def rewriteElems(elems: Seq[Ast.Element]): Seq[Ast.Element] = {
    var d = elems
    d = d.map(rewriteElem)
    for (rule <- rules) {
      d = rule.rewriteSequence(d)
    }
    d
  }

  sealed abstract class Rule {
    def rewriteToplevel(doc: Seq[Element]): Seq[Element] = doc

    def rewriteElement(e: Element): Element = e

    def rewriteSequence(es: Seq[Element]): Seq[Element] = es

  }


  object RewriteCodeBlocks extends Rule {
    override def rewriteSequence(doc: Seq[Element]): Seq[Element] = {
      val current = ListBuffer[Element]()
      val res = ListBuffer[Element]()

      def addCodeBlock(): Unit = {
        val list = current.toList
        if (list.nonEmpty) {
          res.addOne(Block("CodeBlock", Ast.elements(list)))
          current.clear()
        }
      }

      for (n <- doc) {
        n match {
          case Block("isamarkuptext", _)
               | Command("isamarkupsection", _) =>
            addCodeBlock()
            res.addOne(n)
          case _ =>
            current.addOne(n)
        }
      }
      if (res.isEmpty) {
        current.toList
      } else {
        addCodeBlock()
        res.toList
      }
    }
  }

  def flatten(e: Element): IterableOnce[Element] = e match {
    case Text(text) =>
      if (text.isEmpty) List()
      else List(e)
    case Block(tag, content) =>
      List(e)
    case Command(tag, content) =>
      List(e)
    case Elements(s) =>
      s.flatMap(flatten)
  }

  object SimplifySeqs extends Rule {



    override def rewriteSequence(es: Seq[Element]): Seq[Element] = {
      es.flatMap(flatten)
    }
  }

  object Itemize extends Rule {


    override def rewriteElement(e: Element): Element = e match {
      case Block("itemize", content) =>
        val sep = separateBy(content) { case Command("item", _) => true }
        Block("itemize", Ast.elements(
          sep.map(e => Command("item", e))
        ))
      case _ => e
    }
  }

  def separateBy(elem: Element, ignoreFirst: Boolean = true)(f: PartialFunction[Element, Boolean]): List[Element] = {
    val res = ListBuffer[Element]()
    val current = ListBuffer[Element]()
    var first = true
    def addItem(): Unit = {
      if (current.nonEmpty) {
        if (!(ignoreFirst && first))
          res.addOne(Ast.elements(current.toList))
        current.clear()
      }
      first = false
    }
    for (e <- flatten(elem)) {
      if (f.isDefinedAt(e) && f(e)) {
        addItem()
      } else {
        current.addOne(e)
      }
    }
    addItem()
    res.toList
  }

}
