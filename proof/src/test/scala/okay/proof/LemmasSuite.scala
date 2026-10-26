package okay.proof

import Formula.*
import Rule.*
import Term.*

/** the library: every lemma proved by the kernel — closed, of no hypothesis, owned — and used */
class LemmasSuite extends munit.FunSuite:
  val k = Kernel(Theory.empty)
  val lemmas = Lemmas(k)

  test("every arithmetic and equality lemma is proved, closed, of no hypothesis, the kernel's own") {
    val all = lemmas.all
    assert(all.length >= 40, all.length.toString)
    for (name, t) <- all do
      assert(t.hyps.isEmpty, s"$name: ${t.hyps}")
      assert(t.concl.free.isEmpty, s"$name: ${t.concl}")
      assert(k.owns(t), name)
  }

  test("the statements are what they say") {
    val x = V("x", Sort.Int)
    val y = V("y", Sort.Int)
    val z = V("z", Sort.Int)
    assertEquals(lemmas.leTrans(Sort.Int).concl, Formula.all(x, y, z)(Imp(And(Le(x, y), Le(y, z)), Le(x, z))))
    assertEquals(lemmas.leTotal(Sort.Int).concl, Formula.all(x, y)(Or(Le(x, y), Le(y, x))))
    assertEquals(lemmas.ltIrrefl(Sort.Int).concl, All(x, Not(Lt(x, x))))
  }

  test("a lemma used: instantiated, then applied") {
    val inst = k.derive(AllE(k.derive(AllE(k.derive(AllE(lemmas.leTrans(Sort.Int), I(1))).toOption.get,
      I(2))).toOption.get, I(3))).toOption.get
    val premise = k.derive(Compute(And(Le(I(1), I(2)), Le(I(2), I(3))))).toOption.get
    assertEquals(k.derive(ImpE(inst, premise)).map(_.concl), Right(Le(I(1), I(3))))
  }

  test("equality and the classical schemas, for any sort and formulas") {
    val acc = Sort.Named("Account")
    assert(lemmas.eqSym(acc).hyps.isEmpty)
    assert(lemmas.eqTrans(acc).hyps.isEmpty)
    val p = Formula.P(Pred("open", Nil), Nil)
    val q = Formula.P(Pred("funded", Nil), Nil)
    assertEquals(lemmas.excludedMiddle(p).concl, Or(p, Not(p)))
    assertEquals(lemmas.contrapositive(p, q).concl, Imp(Imp(p, q), Imp(Not(q), Not(p))))
    assertEquals(lemmas.deMorganAnd(p, q).concl, Imp(Not(And(p, q)), Or(Not(p), Not(q))))
    assertEquals(lemmas.deMorganOr(p, q).concl, Imp(Not(Or(p, q)), And(Not(p), Not(q))))
  }

  test("a lemma is proved once and kept") {
    assert(lemmas.leTrans(Sort.Dec) eq lemmas.leTrans(Sort.Dec))
  }

  test("a lemma of another kernel is refused as a premise here") {
    val other = Lemmas(Kernel(Theory.empty))
    assert(k.derive(AllE(other.leRefl(Sort.Int), I(1))).isLeft)
  }
