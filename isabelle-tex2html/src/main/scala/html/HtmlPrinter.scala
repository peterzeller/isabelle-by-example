package html

import parser.Ast
import parser.Ast._

import scala.collection.mutable.ListBuffer

object HtmlPrinter {

  def printText(t: Text): List[Node] = {
    List(Txt(t.text))
    //    val blocks = t.text.split("\n\n").map(s => <p>{s}</p>)
    //    <div>
    //      {blocks}
    //    </div>
  }


  def printBlock(b: Block): List[Node] = {
    def tag(s: String): List[Node] = List(Tag(s, print(b.content)))

    b.tag match {
      case "itemize" => tag("ul")
      case "CodeBlock" | "isabelle" => List(Tag("code", List(Tag("pre", print(b.content)))))
      case _ =>
        print(b.content)
    }
  }

  def handleCommand(tagValue: String, value: Element): List[Node] = {
    symbols.get(tagValue) match {
      case Some(v) =>
        return List(Txt(v))
      case None =>
    }


    def tag(s: String): List[Node] = List(Tag(s, print(value)))

    tagValue match {
      case "isamarkupsection" => tag("h1")
      case "item" => tag("li")
      case "setisabellecontext" => List()
      case "isanewline" => List(Tag("br", List()))
      case _ => print(value)
    }
  }

  def printCommand(c: Command): List[Node] =
    handleCommand(c.tag, c.content)

  def printElements(s: Elements): List[Node] =
    printElements(s.s)

  def printElements(s: Seq[Element]): List[Node] =
    s.flatMap(print).toList

  def print(node: Ast.Element): List[Node] = node match {
    case t: Text => printText(t)
    case b: Block => printBlock(b)
    case c: Command => printCommand(c)
    case s: Elements => printElements(s)
  }

  case class PrintContext(sb: StringBuilder, indent: Int, inPre: Boolean) {
    def append(value: String): StringBuilder = sb.append(value)

    def plusIndent: PrintContext = copy(indent = indent + 1)

  }

  sealed abstract class Node {


    private def print(sb: PrintContext): Unit = this match {
      case Tag("br", _) =>
        if (sb.inPre)
          sb.append("\n")
        else
          sb.append("<br/>")
      case Tag(tag, content) =>
        var sb2 = sb
        if (tag == "pre")
          sb2 = sb2.copy(inPre = true)
        val big = isBig
        sb2.append("<").append(tag).append(">")
        if (big) newLine(sb2.plusIndent)
        for (c <- content) {
          c.print(sb2.plusIndent)
        }
        if (big) newLine(sb2)
        sb2.append("</").append(tag).append(">")
      case Txt(text) =>
        if (sb.inPre)
          sb.append(text
            .replaceAll("\n", " ")
            .replaceAll("\\\\ ", "\u0000")
            .replaceAll(" +", "")
            .replaceAll("\u0000", " ")
          )
        else {
          val lines = text.split("\n")
          for (line <- lines) {
            newLine(sb)
            sb.append(line)
          }
        }
    }

    private def newLine(sb: PrintContext): Unit = {
      sb.append("\n")
      if (!sb.inPre) {
        for (_ <- 0 to sb.indent)
          sb.append("  ")
      }
    }

    override def toString: String = {
      val sb = new StringBuilder()
      print(PrintContext(sb, 0, false))
      sb.toString()
    }

    private def isBig: Boolean = this match {
      case Tag(tag, content) =>
        tag != "pre" &&
          content.exists(n => n.isInstanceOf[Tag] || n.isBig)
      case Txt(text) => text.contains("\n")
    }

  }

  case class Tag(tag: String, content: List[Node]) extends Node

  case class Txt(text: String) extends Node


  val symbols: Map[String, String] = Map(
    "isachardoublequoteopen" -> "\"",
    "isachardoublequoteclose" -> "\"",
    "isacharbackquoteopen" -> "\"",
    "isacharbackquoteclose" -> "\"",
    "isacharverbatimopen" -> "\"",
    "isacharverbatimclose" -> "\"",
    "isacartoucheopen" -> "\"",
    "isacartoucheclose" -> "\"",
    "isacharbang" -> "!",
    "isachardoublequote" -> "\"",
    "isachardoublequoteopen" -> "\"",
    "isachardoublequoteclose" -> "\"",
    "isacharhash" -> "#",
    "isachardollar" -> "$",
    "isacharpercent" -> "%",
    "isacharampersand" -> "&",
    "isacharprime" -> "'",
    "isacharparenleft" -> "(",
    "isacharparenright" -> ")",
    "isacharasterisk" -> "*",
    "isacharplus" -> "+",
    "isacharcomma" -> ",",
    "isacharminus" -> "-",
    "isachardot" -> ".",
    "isacharslash" -> "/",
    "isacharcolon" -> ":",
    "isacharsemicolon" -> ";",
    "isacharless" -> "<",
    "isacharequal" -> "=",
    "isachargreater" -> ">",
    "isacharquery" -> "?",
    "isacharat" -> "@",
    "isacharbrackleft" -> "[",
    "isacharbackslash" -> "\\",
    "isacharbrackright" -> "]",
    "isacharcircum" -> "^",
    "isacharunderscore" -> "_",
    "isacharunderscorekeyword" -> "}",
    "isacharbackquote" -> "`",
    "isacharbackquoteopen" -> "`",
    "isacharbackquoteclose" -> "`",
    "isacharbraceleft" -> "{",
    "isacharbar" -> "|",
    "isacharbraceright" -> "}",
    "isachartilde" -> "~"

  )

}
