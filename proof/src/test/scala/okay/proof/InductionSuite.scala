package okay.proof

import Formula.*
import Rule.*
import Term.*

/** universality: a statement about every natural number, by induction — the kernel's rules called directly */
class InductionSuite extends munit.FunSuite:
  val sumFn = Fn("sum", List(Sort.Int), Sort.Int)
  def sum(t: Term) = Ap(sumFn, List(t))
  def plus(a: Term, b: Term) = Ap(Fns.add, List(a, b))
  val n = V("n", Sort.Int)
  val a = V("a", Sort.Int)
  val b = V("b", Sort.Int)
  val theory = Theory("sums",
    "sum0" -> Eq(sum(I(0)), I(0)),
    "sumS" -> All(n, Imp(Le(I(0), n), Eq(sum(plus(n, I(1))), plus(sum(n), plus(n, I(1)))))),
    "pos" -> Formula.all(a, b)(Imp(And(Le(I(0), a), Le(I(0), b)), Le(I(0), plus(a, b)))))
  val k = Kernel(theory)
  def ok(r: Rule): Thm = k.derive(r).fold(e => fail(s"refused: $e"), identity)

  /** from `s = u`, `u = s` */
  def sym(e: Thm): Thm =
    val Eq(s, _) = e.concl: @unchecked
    val z = Logic.fresh(V("z", Logic.sortOf(s).get), s.free)
    ok(Subst(e, z, Eq(z, s), ok(Refl(s))))

  test("∀n. 0 ≤ n → 0 ≤ sum(n)") {
    val x = V("x", Sort.Int)
    val z = V("z", Sort.Int)
    val f = Le(I(0), sum(x))
    // base: 0 ≤ sum(0), from 0 ≤ 0 and sum(0) = 0
    val base = ok(Subst(sym(ok(Axiom("sum0"))), z, Le(I(0), z), ok(Compute(Le(I(0), I(0))))))
    // step: under 0 ≤ x ∧ 0 ≤ sum(x), 0 ≤ sum(x + 1)
    val hyp = And(Le(I(0), x), f)
    val h = ok(Assume(hyp))
    val x0 = ok(AndE1(h))
    val s0 = ok(AndE2(h))
    val pos = ok(Axiom("pos"))
    val x1 = ok(ImpE(ok(AllE(ok(AllE(pos, x)), I(1))), ok(AndI(x0, ok(Compute(Le(I(0), I(1))))))))
    val total = ok(ImpE(ok(AllE(ok(AllE(pos, sum(x))), plus(x, I(1)))), ok(AndI(s0, x1))))
    val unfold = ok(ImpE(ok(AllE(ok(Axiom("sumS")), x)), x0))
    val next = ok(Subst(sym(unfold), z, Le(I(0), z), total))
    val step = ok(AllI(x, ok(ImpI(hyp, next))))
    val all = ok(Induct(x, f, base, step))
    assertEquals(all.concl, All(x, Imp(Le(I(0), x), f)))
    assertEquals(all.hyps, Set.empty[Formula])
    // and used: 0 ≤ sum(5)
    val five = ok(ImpE(ok(AllE(all, I(5))), ok(Compute(Le(I(0), I(5))))))
    assertEquals(five.concl, Le(I(0), sum(I(5))))
    // the certificate checks again, in a kernel of the same theory
    assertEquals(Certificate.check(Certificate.of(all), Kernel(theory)).map(_.concl), Right(all.concl))
  }

  test("induction refuses a step that is not the step") {
    val x = V("x", Sort.Int)
    val f = Le(I(0), x)
    val base = ok(Compute(Le(I(0), I(0))))
    // ∀x. 0 ≤ x ∧ f → f: f again, not f at x + 1
    val hyp = And(Le(I(0), x), f)
    val wrong = ok(AllI(x, ok(ImpI(hyp, ok(AndE2(ok(Assume(hyp))))))))
    assert(k.derive(Induct(x, f, base, wrong)).left.exists(_.contains("the step")))
  }

/** the same theorem with no axiom about addition: the step by linear arithmetic, from the definition and the
 * hypothesis — `Linarith` instead of a `pos` axiom */
class InductionByArithmeticSuite extends munit.FunSuite:
  val sumFn = Fn("sum", List(Sort.Int), Sort.Int)
  def sum(t: Term) = Ap(sumFn, List(t))
  def plus(a: Term, b: Term) = Ap(Fns.add, List(a, b))
  val n = V("n", Sort.Int)
  val theory = Theory("sums",
    "sum0" -> Eq(sum(I(0)), I(0)),
    "sumS" -> All(n, Imp(Le(I(0), n), Eq(sum(plus(n, I(1))), plus(sum(n), plus(n, I(1)))))))
  val k = Kernel(theory)
  def ok(r: Rule): Thm = k.derive(r).fold(e => fail(s"refused: $e"), identity)
  def arith(goal: Formula, theorems: Thm*): Thm =
    Linarith.decide(k, goal, Nil, theorems.toList).fold(e => fail(e), _.getOrElse(fail(s"no certificate for $goal")))

  test("∀n. 0 ≤ n → 0 ≤ sum(n), each arithmetic step by a certificate") {
    val x = V("x", Sort.Int)
    val f = Le(I(0), sum(x))
    val base = arith(Le(I(0), sum(I(0))), ok(Axiom("sum0")))
    val hyp = And(Le(I(0), x), f)
    val h = ok(Assume(hyp))
    val unfold = ok(ImpE(ok(AllE(ok(Axiom("sumS")), x)), ok(AndE1(h))))
    val next = arith(Le(I(0), sum(plus(x, I(1)))), ok(AndE1(h)), ok(AndE2(h)), unfold)
    val step = ok(AllI(x, ok(ImpI(hyp, next))))
    val all = ok(Induct(x, f, base, step))
    assertEquals(all.concl, All(x, Imp(Le(I(0), x), f)))
    assertEquals(all.hyps, Set.empty[Formula])
    assertEquals(Certificate.check(Certificate.of(all), Kernel(theory)).map(_.concl), Right(all.concl))
  }
