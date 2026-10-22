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
    Test / fork := true,
    // every ```scala block of README.md and docs/: compiled, a page an object, run by DocsSuite
    Test / sourceGenerators += Def.task {
      val base = baseDirectory.value
      val out = (Test / sourceManaged).value / "docs"
      val Block = "(?s)```scala\\n(.*?)```".r
      val pages = ((base / "docs") ** "*.md").get.sortBy(_.getPath) :+ (base / "README.md")
      val made = pages.flatMap { md =>
        val blocks = Block.findAllMatchIn(IO.read(md)).map(_.group(1)).toList
        if (blocks.isEmpty) None
        else {
          val name = "Docs_" + md.relativeTo(base).get.getPath.replaceAll("[^A-Za-z0-9]", "_")
          val body = blocks.mkString("\n").linesIterator.map(l => if (l.isEmpty) l else "  " + l).mkString("\n")
          val f = out / s"$name.scala"
          IO.write(f, s"package docs\n\nobject $name:\n$body\n")
          Some(name -> f)
        }
      }
      val suite = out / "DocsSuite.scala"
      IO.write(suite, "package docs\n\n/** each page's examples run: its object loaded */\nclass DocsSuite extends munit.FunSuite:\n" +
        made.map { case (n, _) => s"""  test("$n") { assert($n.hashCode != 0 || true) }""" + "\n" }.mkString)
      made.map(_._2) :+ suite
    }.taskValue)
