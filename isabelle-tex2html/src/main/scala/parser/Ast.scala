package parser

object Ast {
  def elements(es: Seq[Element]): Element =
    if (es.size == 1) es.head
    else Elements(es)

  def elements(es: Option[Seq[Element]]): Element =
    elements(es.getOrElse(Seq()))

  sealed abstract class Element {

    private def print(sb: StringBuilder, indent: Int): Unit = this match {
      case Text(text) =>
        for (line <- text.linesIterator) {
          sb.append("\"").append(line.replace("\n","\\n")).append("\"")
        }
      case Block(tag, content) =>
        newLine(sb, indent)
        sb.append("BEGIN ").append(tag)
        newLine(sb, indent+1)
        content.print(sb, indent + 1)
        newLine(sb, indent)
        sb.append("END ").append(tag)
      case Command(tag, content) =>
        sb.append("\\").append(tag).append("{")
        content.print(sb, indent + 1)
        sb.append("}")
      case Elements(es) =>
        for (e <- es) {
          e.print(sb, indent + 1)
          newLine(sb, indent)
        }
    }

    private def newLine(sb: StringBuilder, i: Int): Unit = {
      sb.append("\n")
      for (_ <- 0 to i)
        sb.append("  ")
    }

    override def toString: String = {
      val sb = new StringBuilder()
      print(sb, 0)
      sb.toString()
    }


  }

  case class Text(text: String) extends Element

  case class Block(tag: String, content: Element) extends Element

  case class Command(tag: String, content: Element) extends Element

  case class Elements(s: Seq[Element]) extends Element


}
