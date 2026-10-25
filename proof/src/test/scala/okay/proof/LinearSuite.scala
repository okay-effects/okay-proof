package okay.proof

import Formula.*
import Rule.*
import Term.*

/** the kernel's linear rules: what each gives, and what it refuses */
class LinearSuite extends munit.FunSuite:
  val k = Kernel(Theory.empty)
  val x = V("x", Sort.Int)
  val y = V("y", Sort.Int)
  val z = V("z", Sort.Int)
  val p = V("p", Sort.Dec)
  def add(a: Term, b: Term) = Ap(Fns.add, List(a, b))
  def mul(c: Int, a: Term) = Ap(Fns.mul, List(I(c), a))
  def ok(r: Rule): Thm = k.derive(r).fold(e => fail(s"refused: $e"), identity)
  def refused(r: Rule, part: String): Unit = k.derive(r) match
    case Left(e) => assert(e.contains(part), e)
    case Right(t) => fail(s"derived $t")

  test("Norm: identities of linear arithmetic, over atoms, in one step") {
    ok(Norm(Eq(add(x, y), add(y, x))))
    ok(Norm(Le(x, add(x, I(1)))))
    ok(Norm(Lt(x, add(x, I(1)))))
    ok(Norm(Eq(Ap(Fns.dadd, List(p, D(BigDecimal("0.10")))), Ap(Fns.dadd, List(D(BigDecimal("0.1")), p)))))
    val f = Fn("f", List(Sort.Int), Sort.Int)
    ok(Norm(Eq(Ap(f, List(add(x, I(1)))), Ap(f, List(add(I(1), x)))))) // f's argument in canonical form
    refused(Norm(Le(x, add(x, I(-1)))), "is false")
    refused(Norm(Le(x, y)), "more than a constant")
    refused(Norm(Not(Le(x, y))), "not a comparison")
  }

  test("LinComb: non-negative multiples of inequalities, any of equations, summed") {
    val xy = ok(Assume(Le(x, y)))
    val yz = ok(Assume(Le(y, z)))
    val sum = ok(LinComb(List(xy -> 1, yz -> 1)))
    assertEquals(Linear.comparison(sum.concl).map(_._1), Linear.comparison(Le(x, z)).map(_._1))
    assertEquals(sum.hyps, Set[Formula](Le(x, y), Le(y, z)))
    refused(LinComb(List(xy -> -1)), "negative coefficient")
    refused(LinComb(List(xy -> BigDecimal("0.5"))), "not an integer")
    val e = ok(Assume(Eq(x, I(3))))
    ok(LinComb(List(e -> -2)))
    refused(LinComb(List(xy -> 1, ok(Assume(Le(p, p))) -> 1)), "two sorts")
    refused(LinComb(Nil), "no premises")
  }

  test("over Int a strict comparison is + 1 ≤; the negated orders read as their converses") {
    val lt = ok(LinComb(List(ok(Assume(Lt(x, y))) -> 1)))
    assertEquals(Linear.comparison(lt.concl).map(_._1), Linear.comparison(Le(add(x, I(1)), y)).map(_._1))
    val notLe = ok(LinComb(List(ok(Assume(Not(Le(p, D(BigDecimal(1)))))) -> 1)))
    assert(notLe.concl.isInstanceOf[Lt], notLe.concl.toString) // over Dec, ¬(p ≤ 1) is 0 < p - 1
  }

  test("Tighten: over Int, 2x ≥ 1 gives x ≥ 1; not over Dec, not without an atom") {
    val t = ok(Tighten(ok(Assume(Le(I(1), mul(2, x))))))
    assertEquals(Linear.comparison(t.concl).map(_._1), Linear.comparison(Le(I(1), x)).map(_._1))
    refused(Tighten(ok(Assume(Le(D(BigDecimal(1)), Ap(Fns.dmul, List(D(BigDecimal(2)), p)))))), "not 0 ≤ F over Int")
    refused(Tighten(ok(Compute(Le(I(0), I(3))))), "not 0 ≤ F over Int")
  }

  test("Antisym: a ≤ b and b ≤ a give a = b") {
    assertEquals(ok(Antisym(ok(Assume(Le(x, y))), ok(Assume(Le(y, x))))).concl, Eq(x, y))
    refused(Antisym(ok(Assume(Le(x, y))), ok(Assume(Le(x, y)))), "not a ≤ b and b ≤ a")
  }
