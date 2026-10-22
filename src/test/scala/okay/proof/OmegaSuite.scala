package okay.proof

import Formula.*
import Term.*

/** the integers decided: where the rationals have a solution and the integers none, the Omega test's refutation */
class OmegaSuite extends munit.FunSuite:
  val k = Kernel(Theory.empty)
  val (x, y, z) = (V("x", Sort.Int), V("y", Sort.Int), V("z", Sort.Int))
  def lin(cs: (Int, V)*)(c: Int = 0): Term =
    (cs.map((n, v) => Ap(Fns.mul, List(I(n), v)): Term) :+ I(c)).reduceLeft((a, b) => Ap(Fns.add, List(a, b)))
  val falsum = Lt(I(1), I(0))

  def refuted(facts: Formula*): Option[Thm] =
    Linarith.decide(k, falsum, facts.toList).fold(e => fail(s"a step refused: $e"), identity)

  test("Pugh's example: 27 ≤ 11x + 13y ≤ 45, −10 ≤ 7x − 9y ≤ 4 — rational solutions, no integer one") {
    val facts = List(Le(I(27), lin(11 -> x, 13 -> y)()), Le(lin(11 -> x, 13 -> y)(), I(45)),
      Le(I(-10), lin(7 -> x, -9 -> y)()), Le(lin(7 -> x, -9 -> y)(), I(4)))
    val integer = for a <- -60 to 60; b <- -60 to 60
      if 27 <= 11 * a + 13 * b && 11 * a + 13 * b <= 45 && -10 <= 7 * a - 9 * b && 7 * a - 9 * b <= 4 yield (a, b)
    assertEquals(integer, Vector.empty)
    assertEquals(Linarith.refute(facts, Nil, Sort.Int), None, "the rationals' elimination refutes it already")
    val t = refuted(facts*).getOrElse(fail("no refutation"))
    assert(t.hyps.subsetOf(facts.toSet))
    assertEquals(Certificate.check(Certificate.of(t), Kernel(Theory.empty)).map(_.concl), Right(falsum))
  }

  test("an equation with no coefficient ±1 (mod̂, a fresh σ): 3x + 5y = 1 in the box 0..1 has no solution") {
    val facts = List(Eq(lin(3 -> x, 5 -> y)(), I(1)), Le(I(0), x), Le(x, I(1)), Le(I(0), y), Le(y, I(1)))
    assert(refuted(facts*).isDefined)
    assertEquals(refuted(Eq(lin(3 -> x, 5 -> y)(), I(1))), None) // x = 2, y = −1
  }

  test("an equation the gcd does not divide: 6x + 9y = 4") {
    assert(refuted(Eq(lin(6 -> x, 9 -> y)(), I(4))).isDefined)
    assertEquals(refuted(Eq(lin(6 -> x, 9 -> y)(), I(3))), None)
  }

  test("a goal, not only a contradiction: 2 ≤ 3x ≤ 4 ⊢ x = 1") {
    val t = Linarith.decide(k, Eq(x, I(1)), List(Le(I(2), lin(3 -> x)()), Le(lin(3 -> x)(), I(4))))
    assertEquals(t.map(_.map(_.concl)), Right(Some(Eq(x, I(1)))))
  }

  test("COMPLETE: 300 random systems in a box — refuted exactly when the box has no integer solution") {
    val rnd = scala.util.Random(20261022)
    val vars = Vector(x, y, z)
    var (refutedN, solvableN) = (0, 0)
    for _ <- 1 to 300 do
      val n = 2 + rnd.nextInt(2)
      val vs = vars.take(n)
      val box = vs.flatMap(v => List(Le(I(-4), v), Le(v, I(4))))
      val cs = Vector.fill(2 + rnd.nextInt(3)) {
        val coeffs = vs.map(_ => rnd.nextInt(13) - 6)
        val c = rnd.nextInt(21) - 10
        (coeffs, c, rnd.nextInt(3))
      }
      def term(coeffs: Vector[Int]) = lin(coeffs.zip(vs)*)()
      val facts = box ++ cs.map { (coeffs, c, kind) =>
        kind match
          case 0 => Le(term(coeffs), I(c))
          case 1 => Lt(I(c), term(coeffs))
          case _ => Eq(term(coeffs), I(c))
      }
      def holds(p: Vector[Int]) = cs.forall { (coeffs, c, kind) =>
        val s = coeffs.zip(p).map(_ * _).sum
        kind match
          case 0 => s <= c
          case 1 => c < s
          case _ => s == c
      }
      val points = vs.indices.foldLeft(Vector(Vector.empty[Int]))((acc, _) => for p <- acc; v <- -4 to 4 yield p :+ v)
      val solvable = points.exists(holds)
      val got = refuted(facts*)
      if solvable then
        assertEquals(got, None, s"refuted a solvable system: $facts")
        solvableN += 1
      else
        assert(got.isDefined, s"no refutation of an unsolvable system: $facts")
        refutedN += 1
    assert(refutedN > 50 && solvableN > 50, s"refuted $refutedN, solvable $solvableN")
  }

  test("COMPLETE where it is hard: two thin strips crossing — rational points, often no integer one; the shadows") {
    def strip(a: Int, b: Int): Term = lin(a -> x, b -> y)()
    val rnd = scala.util.Random(11)
    var (refutedN, solvableN, split, pastRationals) = (0, 0, 0, 0)
    for _ <- 1 to 300 do
      def c() = (3 + rnd.nextInt(13)) * (if rnd.nextBoolean() then 1 else -1)
      val (a1, b1, a2, b2) = (c(), c(), c(), c())
      val (l1, w1, l2, w2) = (rnd.nextInt(81) - 40, rnd.nextInt(7), rnd.nextInt(81) - 40, rnd.nextInt(7))
      val box = List(x, y).flatMap(v => List(Le(I(-40), v), Le(v, I(40))))
      val facts = box ++ List(Le(I(l1), strip(a1, b1)), Le(strip(a1, b1), I(l1 + w1)),
        Le(I(l2), strip(a2, b2)), Le(strip(a2, b2), I(l2 + w2)))
      val solvable = (for p <- -40 to 40; q <- -40 to 40 yield (p, q)).exists { (p, q) =>
        val (s1, s2) = (a1 * p + b1 * q, a2 * p + b2 * q)
        l1 <= s1 && s1 <= l1 + w1 && l2 <= s2 && s2 <= l2 + w2
      }
      if !solvable && Linarith.refute(facts, Nil, Sort.Int).isEmpty then pastRationals += 1
      // the Omega test alone, its steps checked by the kernel
      Omega.refute(facts, Nil).map(plan => okay.effects.run(Infer.by(k)(Omega.emit[Infer](plan)))) match
        case Some(Left(why)) => fail(s"a step refused: $why")
        case Some(Right(t)) =>
          assert(!solvable, s"refuted a solvable system: $facts")
          assertEquals(t.concl, False)
          assert(t.hyps.subsetOf(facts.toSet))
          refutedN += 1
          if Certificate.of(t).contains("\"rule\":\"OrE\"") then split += 1
        case None =>
          assert(solvable, s"no refutation of an unsolvable system: $facts")
          solvableN += 1
    assert(refutedN > 100 && solvableN > 30 && split > 20 && pastRationals > 20,
      s"refuted $refutedN, solvable $solvableN, by cases $split, past the rationals' elimination $pastRationals")
  }
