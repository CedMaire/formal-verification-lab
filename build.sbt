ThisBuild / scalaVersion     := "2.12.8"
ThisBuild / version          := "1.0.0"
ThisBuild / organization     := "ch.epfl.lara"
ThisBuild / organizationName := "LARA"

lazy val root = (project in file("."))
  .settings(
    name := "lcf-theorems",
  )
  .dependsOn(lcf)

lazy val lcf = (project in file("lcf"))
  .settings(
    name := "lcf",
  )
  .dependsOn(fol)

lazy val fol = (project in file("fol"))
  .settings(
    name := "fol",
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-reflect" % scalaVersion.value
    ),
  )
