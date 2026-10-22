package okay.proof

import Formula.*
import Term.*

/** linear arithmetic decided: a certificate found outside the kernel, checked inside */
class LinarithSuite extends munit.FunSuite:
  val k = Kernel(Theory.empty)
  def iv(n: String) = V(n, Sort.Int)
  def dv(n: String) = V(n, Sort.Dec)
  val (x, y, z, w) = (iv("x"), iv("y"), iv("z"), iv("w"))
  val (a, b, c) = (dv("a"), dv("b"), dv("c"))
  def add(p: Term, q: Term) = Ap(Fns.add, List(p, q))
  def dadd(p: Term, q: Term) = Ap(Fns.dadd, List(p, q))
  def mul(n: Int, p: Term) = Ap(Fns.mul, List(I(n), p))
  def dec(s: String): Term = D(BigDecimal(s))

  def proved(goal: Formula, facts: Formula*): Option[Thm] =
    Linarith.decide(k, goal, facts.toList).fold(e => fail(s"a step refused: $e"), identity)
  def holds(goal: Formula, facts: Formula*): Thm =
    val t = proved(goal, facts*).getOrElse(fail(s"no proof of $goal"))
    assertEquals(t.concl, goal)
    assert(t.hyps.subsetOf(facts.toSet), t.hyps.toString)
    t

  test("a chain, over Int and over Dec") {
    holds(Le(x, w), Le(x, y), Le(y, z), Le(z, w))
    holds(Le(a, c), Le(a, b), Le(b, c))
  }

  test("strict and not: x < y ∧ y ≤ z ⊢ x < z; ¬(x ≤ y) ⊢ y < x") {
    holds(Lt(x, z), Lt(x, y), Le(y, z))
    holds(Lt(y, x), Not(Le(x, y)))
    holds(Not(Lt(z, x)), Le(x, y), Le(y, z))
  }

  test("equations: solved for, and an equation proved") {
    holds(Eq(x, I(4)), Eq(x, add(y, I(1))), Eq(y, I(3)))
    holds(Eq(dadd(a, b), dec("0.30")), Eq(a, dec("0.10")), Eq(b, dec("0.20")))
  }

  test("the integers are not the rationals: x < y < x + 1 is impossible over Int, possible over Dec") {
    holds(Not(Lt(x, y)), Lt(y, add(x, I(1))))
    assertEquals(proved(Not(Lt(a, b)), Lt(b, dadd(a, dec("1")))), None)
  }

  test("a cut over Int: 2x = 1 has no integer solution") {
    holds(Lt(I(1), I(0)), Eq(mul(2, x), I(1)))
    holds(Le(I(1), x), Le(I(1), mul(2, x))) // 2x ≥ 1 ⊢ x ≥ 1
  }

  test("atoms: terms of one's own, compared by their canonical form") {
    val sum = Fn("sum", List(Sort.Int), Sort.Int)
    holds(Le(I(0), Ap(sum, List(add(x, I(1))))), Le(I(0), Ap(sum, List(add(I(1), x)))))
    val limit = Fn("limit", Nil, Sort.Dec)
    holds(Le(dadd(Ap(limit, Nil), dec("-500.00")), dec("500.00")), Eq(Ap(limit, Nil), dec("1000.00")))
  }

  test("what does not follow is not proved") {
    assertEquals(proved(Le(y, x), Le(x, y)), None)
    assertEquals(proved(Eq(x, y), Le(x, y)), None)
  }

  test("contradictory facts prove anything they compare") {
    holds(Lt(I(1), I(0)), Lt(x, y), Lt(y, x))
  }

  test("a decision's certificate is checked again") {
    val t = holds(Lt(x, z), Lt(x, y), Le(y, z))
    assertEquals(Certificate.check(Certificate.of(t), Kernel(Theory.empty)).map(_.concl), Right(t.concl))
  }
