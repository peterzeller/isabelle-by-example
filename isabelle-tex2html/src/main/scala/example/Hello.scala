package example

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Paths}

import html.{HtmlPrinter, Preprocess}
import parser.{Ast, TexParser}

import scala.io.Source
import scala.util.{Failure, Success, Try}


object Hello{

  def main(args: Array[String]): Unit = {
    val f = new File("../output/document/test.tex")
    val input = new String(Files.readAllBytes(f.toPath), UTF_8)


    val r: Try[Seq[Ast.Element]] = TexParser.run(input)


    r match {
      case Failure(exception) =>
        println("ERROR:" + exception.getMessage)
      case Success(elems) =>

        Files.write(Paths.get("target/elems.html"), elems.mkString.getBytes(UTF_8))

        val pre = Preprocess.rewrite(elems)
        Files.write(Paths.get("target/pre.html"), pre.mkString.getBytes(UTF_8))

        val html = HtmlPrinter.printElements(pre)
        Files.write(Paths.get("target/out.html"), html.mkString.getBytes(UTF_8))

    }

  }
}

