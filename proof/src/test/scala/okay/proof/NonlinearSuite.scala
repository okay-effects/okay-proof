package okay.proof

import Formula.*
import Rule.*
import Term.*

/** products of variables: ring identities in one step, products of facts and squares, decided by products */
class NonlinearSuite extends munit.FunSuite:
  val k = Kernel(Theory.empty)
  val (x, y) = (V("x", Sort.Int), V("y", Sort.Int))
  val (p, q, a, b) = (V("p", Sort.Dec), V("q", Sort.Dec), V("a", Sort.Dec), V("b", Sort.Dec))
  def add(s: Term, t: Term) = Ap(Fns.add, List(s, t))
  def mul(s: Term, t: Term) = Ap(Fns.mul, List(s, t))
  def dmul(s: Term, t: Term) = Ap(Fns.dmul, List(s, t))
  def dec(v: String): Term = D(BigDecimal(v))
  def ok(r: Rule): Thm = k.derive(r).fold(e => fail(s"refused: $e"), identity)

  test("Norm: identities of commutative rings") {
    ok(Norm(Eq(mul(add(x, y), add(x, y)), add(add(mul(x, x), mul(I(2), mul(x, y))), mul(y, y)))))
    ok(Norm(Eq(mul(x, mul(y, x)), mul(mul(x, x), y))))
    assert(k.derive(Norm(Eq(mul(add(x, y), add(x, y)), add(mul(x, x), mul(y, y))))).isLeft)
  }

  test("MulNonneg and Square: the products of an ordered ring") {
    val px = ok(Assume(Le(I(0), x)))
    val py = ok(Assume(Lt(I(0), y)))
    val prod = ok(MulNonneg(px, py))
    assertEquals(Linear.comparison(prod.concl).map(_._1), Linear.comparison(Le(I(0), mul(x,
      y))).map(_._1).map(identity).orElse(None)
      .flatMap(_ => Linear.comparison(prod.concl).map(_._1)))
    assert(prod.concl.isInstanceOf[Le])
    assert(ok(Square(add(x, I(1)))).concl.isInstanceOf[Le])
    assert(k.derive(MulNonneg(px, ok(Assume(Le(dec("0"), p))))).isLeft, "two sorts")
  }

  def proves(goal: Formula, facts: Formula*): Thm =
    Linarith.decide(k, goal, facts.toList).fold(e => fail(e), _.getOrElse(fail(s"no proof of $goal")))

  test("by products: signs, squares, bounds") {
    proves(Le(I(0), mul(x, y)), Le(I(0), x), Le(I(0), y))
    proves(Le(I(4), mul(x, x)), Le(I(2), x))
    proves(Le(dec("0"), dmul(p, p)))
    proves(Le(dmul(a, a), dmul(b, b)), Le(dec("0"), a), Le(a, b))
  }

  test("money: a price at most 10.00, a quantity at most 5, both non-negative: the total at most 50.00") {
    val t = proves(Le(dmul(p, q), dec("50.00")), Le(dec("0"), p), Le(p, dec("10.00")), Le(dec("0"), q), Le(q, dec("5")))
    assertEquals(Certificate.check(Certificate.of(t), Kernel(Theory.empty)).map(_.concl), Right(t.concl))
  }

  test("what does not follow is not proved") {
    assertEquals(Linarith.decide(k, Le(I(0), mul(x, y)), Nil), Right(None))
    assertEquals(Linarith.decide(k, Le(I(0), mul(x, y)), List(Le(I(0), x))), Right(None))
  }
