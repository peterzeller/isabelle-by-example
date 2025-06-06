import Dependencies._

ThisBuild / scalaVersion     := "2.13.1"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "com.example"
ThisBuild / organizationName := "example"

lazy val root = (project in file("."))
  .settings(
    name := "isabelle-tex2html",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2",
    libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.2.0"
  )

// See https://www.scala-sbt.org/1.x/docs/Using-Sonatype.html for instructions on how to publish to Sonatype.
