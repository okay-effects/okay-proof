package okay.proof

import Formula.*
import Rule.*
import Term.*

/** each rule: what it gives, and what it refuses */
class KernelSuite extends munit.FunSuite:
  val k = Kernel(Theory.empty)
  val x = V("x", Sort.Int)
  val y = V("y", Sort.Int)
  def ok(r: Rule): Thm = k.derive(r).fold(e => fail(s"refused: $e"), identity)
  def refused(r: Rule, part: String): Unit = k.derive(r) match
    case Left(e) => assert(e.contains(part), e)
    case Right(t) => fail(s"derived $t")

  test("assume, ∧ in and out, → in and out") {
    val p = Lt(x, I(5))
    val h = ok(Assume(p))
    val both = ok(AndI(h, h))
    val imp = ok(ImpI(p, ok(AndE1(both))))
    assertEquals(imp.hyps, Set.empty[Formula])
    assertEquals(imp.concl, Imp(p, p))
    assertEquals(ok(ImpE(imp, h)).concl, p)
    refused(ImpE(imp, ok(Assume(Lt(y, I(5))))), "is not")
  }

  test("compute: exact arithmetic in one step; false and the uncomputable refused") {
    val sum = Eq(Ap(Fns.dadd, List(D(BigDecimal("0.1")), D(BigDecimal("0.2")))), D(BigDecimal("0.3")))
    assertEquals(ok(Compute(sum)).concl, sum)
    refused(Compute(Lt(I(3), I(2))), "computed false")
    refused(Compute(Eq(Bank.limit(Bank.teller), Bank.dec("1"))), "not computable")
    refused(Compute(Eq(Ap(Fns.div, List(I(1), I(0))), I(0))), "not computable")
    refused(Compute(Lt(x, I(2))), "not closed")
  }

  test("rounding is a function, named, and how: half to even, half up; division to a scale; floor division") {
    def is(t: Term, v: String) = assert(k.derive(Compute(Eq(t, Bank.dec(v)))).isRight, s"$t is not $v")
    is(Ap(Fns.round, List(Bank.dec("2.345"), I(2))), "2.34")
    is(Ap(Fns.roundHalfUp, List(Bank.dec("2.345"), I(2))), "2.35")
    is(Ap(Fns.ddiv, List(Bank.dec("10"), Bank.dec("3"), I(2))), "3.33")
    assert(k.derive(Compute(Eq(Ap(Fns.div, List(I(-7), I(2))), I(-4)))).isRight)
    assert(k.derive(Compute(Eq(Ap(Fns.mod, List(I(-7), I(2))), I(1)))).isRight)
  }

  test("texts: take, takeRight, indexOf by characters (code points, as Lean's); wrong values and sorts refused") {
    def is(t: Term, v: Term) = assert(k.derive(Compute(Eq(t, v))).isRight, s"$t is not $v")
    def isNot(t: Term, v: Term) = refused(Compute(Eq(t, v)), "computed false")
    val path = S("/ws/a\uD83D\uDE00b.txt")
    is(Ap(Fns.take, List(path, I(4))), S("/ws/"))
    is(Ap(Fns.take, List(path, I(6))), S("/ws/a\uD83D\uDE00")) // the emoji one character, not two
    is(Ap(Fns.takeRight, List(path, I(4))), S(".txt"))
    is(Ap(Fns.take, List(S("ab"), I(-1))), S(""))
    is(Ap(Fns.take, List(S("ab"), I(9))), S("ab"))
    is(Ap(Fns.takeRight, List(S("ab"), I(9))), S("ab"))
    is(Ap(Fns.indexOf, List(path, S("b.t"))), I(6))
    is(Ap(Fns.indexOf, List(S("abc"), S(""))), I(0))
    is(Ap(Fns.indexOf, List(S("abc"), S("x"))), I(-1))
    isNot(Ap(Fns.take, List(path, I(4))), S("/ws"))
    isNot(Ap(Fns.indexOf, List(path, S("b.t"))), I(7)) // by characters: 7 would be by UTF-16 units
    refused(Compute(Eq(Ap(Fns.take, List(I(1), I(4))), S(""))), "not closed and well-sorted")
  }

  test("∀ in: refused while the variable is free in a hypothesis; ∀ out: no capture") {
    val h = ok(Assume(Le(x, x)))
    refused(AllI(x, h), "free in a hypothesis")
    val refl = ok(Refl(x))
    val all = ok(AllI(x, ok(ImpI(Lt(x, y), refl))))
    // ∀x. x < y → x = x, with x := y: no capture of y, and the bound x renamed where it would be
    assertEquals(ok(AllE(all, y)).concl, Imp(Lt(y, y), Eq(y, y)))
    val nested = ok(AllI(x, ok(Refl(Ap(Fns.add, List(x, y))))))
    val under = Ex(y, Eq(y, y))
    val g = ok(AllI(x, ok(ImpI(under, ok(Assume(under))))))
    assertEquals(ok(AllE(g, y)).concl, Imp(under, under))
    refused(AllE(nested, Bank.dec("1")), "not of")
  }

  test("∃ in and out: the eigenvariable fresh") {
    val p = Lt(I(0), x)
    val withThree = ok(Compute(Lt(I(0), I(3))))
    val ex = ok(ExI(x, p, I(3), withThree))
    assertEquals(ex.concl, Ex(x, p))
    val z = V("z", Sort.Int)
    val inner = ok(Assume(Lt(I(0), z)))
    val ok2 = ok(ExE(ex, z, ok(ImpI(True, ok(Compute(True))))))
    assertEquals(ok2.concl, Imp(True, True))
    refused(ExE(ex, z, inner), "not fresh")
  }

  test("equality: s = u carries a formula from s to u") {
    val e = ok(Assume(Eq(x, I(4))))
    val p = ok(Compute(Lt(I(4), I(5))))
    refused(Subst(e, y, Lt(y, I(5)), p), "is not")
    // from x = 4 and 4 < 5? the shape is f[s/x]: carry x < 5 back from 4 < 5 needs 4 = x — the other direction
    val back = ok(Subst(e, y, Eq(y, x), ok(Refl(x)))) // x = 4 ⊢ 4 = x
    assertEquals(back.concl, Eq(I(4), x))
    assertEquals(ok(Subst(back, y, Lt(y, I(5)), p)).concl, Lt(x, I(5)))
  }

  test("classical: ¬¬f gives f; False gives anything; ¬ in and out") {
    val p = Lt(x, I(1))
    val contra = ok(NotE(ok(Assume(Not(p))), ok(Assume(p))))
    assertEquals(contra.concl, False)
    assertEquals(ok(NotI(Not(p), contra)).concl, Not(Not(p)))
    assertEquals(ok(Classic(ok(NotI(Not(p), contra)))).hyps, Set[Formula](p))
    assertEquals(ok(FalseE(contra, Lt(I(9), I(1)))).concl, Lt(I(9), I(1)))
  }

  test("a theorem of another kernel is refused as a premise") {
    val other = Kernel(Theory("other", "one" -> Eq(I(1), I(2))))
    val bogus = other.derive(Axiom("one")).toOption.get
    refused(AndI(bogus, bogus), "another kernel")
    assert(!k.owns(bogus))
  }

  test("a theory refuses an open or ill-sorted axiom; ill-sorted assumptions are refused") {
    intercept[IllegalArgumentException](Theory("t", "open" -> Lt(x, I(1))))
    intercept[IllegalArgumentException](Theory("t", "sorts" -> Le(I(1), Bank.dec("1"))))
    refused(Assume(Eq(I(1), Bank.dec("1"))), "not well-sorted")
  }
