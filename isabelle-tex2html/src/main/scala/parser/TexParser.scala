package parser

import fastparse._
import NoWhitespace._
import parser.Ast._

import scala.util.{Failure, Success, Try}

object TexParser {

  implicit val whitespace: P[_] => P[Unit] = { implicit ctx: ParsingRun[_] =>
    P("%" ~ noNewline.rep ~ "\n")
  }
  private def noNewline[_: P]: P[Unit] =
      CharPred(c => c != '\n')

  def run(input1: String): Try[Seq[Element]] = {
    // remove comments, since not working in parser
    val input = input1.linesIterator
        .map(l => l.replaceFirst("%.*$", ""))
        .mkString("\n")

      parse(input, parseDocument(_)) match {
      case Parsed.Success(value, index) =>
        Success(value)
      case failure: Parsed.Failure =>
        Failure(Error(failure.msg))
    }
  }

  case class Error(msg: String) extends Exception(msg)

  private def parseDocument[_: P]: P[Seq[Element]] =
    P(parseElements ~ End)

  private def parseElements[_: P]: P[Seq[Element]] =
    P(parseElem.rep)

  private def parseElem[_: P]: P[Ast.Element] =
    P((parseBlock | parseCommand | parseBraces | parseText))


  private def parseBraces[_: P]: P[Elements] = P("{" ~ parseElements ~ "}").map(Ast.Elements)

  private def textChar[_: P]: P[String] =
    P((CharPred(c => c != '\\' && c != '{' && c != '}') | ("\\" ~ ("\\" | "{" | "}" | " "))).!)


  private def letter[_: P]: P[Unit] =
      CharPred(c => Character.isAlphabetic(c))

  private def parseTag[_: P]: P[String] =
    P(letter.rep(1).!)

  private def parseText[_: P]: P[Ast.Text] =
    P(textChar.rep(1)).map(s => Ast.Text(s.mkString("")))

  private def parseBlock[_: P]: P[Block] = P(
    beginTag.flatMap(endTag)
  )

  private def beginTag[_: P]: P[(String, Seq[Element])] =
    P("\\begin{" ~ parseTag ~ "}" ~ parseElements)

  private def endTag[_: P](e: (String, Seq[Element])): P[Block] =
    P("\\end{" + e._1 + "}").map(_ => Ast.Block(e._1, Ast.elements(e._2)))

  private def parseCommand[_: P]: P[Element] =
    P("\\" ~ parseTag ~ ("{" ~ parseElements ~ "}").?)
      .filter(_._1 != "end")
      .map(e => Command(e._1, Ast.elements(e._2)))


}
