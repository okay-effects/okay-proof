import sbtcrossproject.CrossPlugin.autoImport.{crossProject, CrossType}

// okay-proof: a small LCF-style prover — a kernel of first-order logic with equality, induction and exact arithmetic
// by computation — whose inference steps are also an EFFECT of okay-scala's, for audit and control at run time
ThisBuild / scalaVersion := "3.3.8"
ThisBuild / organization := "io.github.okay-effects"
ThisBuild / version := "0.1.0"
ThisBuild / versionScheme := Some("early-semver")
ThisBuild / licenses := List("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.txt"))

/** RELEASES, ON GITHUB PAGES: `sbt publish` writes okay-proof and okay-policy for the JVM and Scala.js, as a Maven
 * repository, into `target/pages-maven/`; that goes to the `gh-pages` branch under `maven/`, served at
 * https://okay-effects.github.io/okay-proof/maven */
val pagesRepository = settingKey[File]("the Maven repository a release is written to, for GitHub Pages")
ThisBuild / pagesRepository := (ThisBuild / baseDirectory).value / "target" / "pages-maven"
ThisBuild / publishTo := Some(MavenCache("pages", (ThisBuild / pagesRepository).value))
ThisBuild / Compile / packageDoc / publishArtifact := false

ThisBuild / resolvers += "okay-scala" at "https://okay-effects.github.io/okay-scala/maven"

ThisBuild / scalacOptions ++= Seq("-deprecation", "-feature", "-Wunused:imports")

/** THE PROVER: the kernel, its effect, search, certificates — on the JVM and in the browser (Scala.js), on okay-scala's
 * effects */
lazy val proof = crossProject(JVMPlatform, JSPlatform).crossType(CrossType.Pure).in(file("proof"))
  .settings(
    name := "okay-proof",
    libraryDependencies ++= Seq(
      "io.github.okay-effects" %%% "okay-scala" % "0.1.1",
      "org.scalameta" %%% "munit" % "1.2.3" % Test))
  .jvmSettings(
    Test / fork := true,
    // every ```scala block of README.md and docs/: compiled, a page an object, run by DocsSuite
    Test / sourceGenerators += Def.task {
      val base = (ThisBuild / baseDirectory).value
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

/** THE POLICY LANGUAGE: parsed, checked, its decisions theorems of the prover — specs/policy.md */
lazy val policy = crossProject(JVMPlatform, JSPlatform).crossType(CrossType.Pure).in(file("policy"))
  .dependsOn(proof)
  .settings(
    name := "okay-policy",
    libraryDependencies += "org.scalameta" %%% "munit" % "1.2.3" % Test)

lazy val root = (project in file(".")).aggregate(proof.jvm, proof.js, policy.jvm, policy.js)
  .settings(publish / skip := true)
