package okay.proof

/** the order of texts by code points (trusted: it orders atoms as Lean does) — the same as by arrays of code points */
class CodePointsSuite extends munit.FunSuite:
  def byArrays(a: String, b: String): Int =
    val (x, y) = (a.codePoints.toArray, b.codePoints.toArray)
    var i = 0
    while i < x.length && i < y.length && x(i) == y(i) do i += 1
    if i < x.length && i < y.length then Integer.compare(x(i), y(i)) else Integer.compare(x.length, y.length)

  test("random texts, with surrogate pairs and prefixes: the same order as before") {
    val r = scala.util.Random(7)
    val alphabet = Vector("a", "b", "z", "é", "😀", "😁", "￿", "1")
    def text = (0 until r.nextInt(6)).map(_ => alphabet(r.nextInt(alphabet.size))).mkString
    for _ <- 0 until 20000 do
      val (a, b) = (text, text)
      assertEquals(Integer.signum(Logic.byCodePoints.compare(a, b)), Integer.signum(byArrays(a, b)), s"$a | $b")
  }
