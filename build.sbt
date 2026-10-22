// okay-proof: a small LCF-style prover — a kernel of first-order logic with equality, induction and exact arithmetic
// by computation — whose inference steps are also an EFFECT of okay-simple's, for audit and control at run time
ThisBuild / scalaVersion := "3.3.8"
ThisBuild / organization := "io.github.okay-effects"
ThisBuild / version := "0.1.0-SNAPSHOT"

resolvers += "okay-effects" at "https://okay-effects.github.io/okay-simple/maven"

lazy val root = (project in file("."))
  .settings(
    name := "okay-proof",
    libraryDependencies ++= Seq(
      "io.github.okay-effects" %% "okay-effects-machine" % "0.1.0",
      "org.scalameta" %% "munit" % "1.2.3" % Test),
    scalacOptions ++= Seq("-deprecation", "-feature", "-Wunused:imports"),
    Test / fork := true)
