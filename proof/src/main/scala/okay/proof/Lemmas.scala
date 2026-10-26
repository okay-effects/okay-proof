package okay.proof

import scala.collection.mutable
import okay.scala3.*
import okay.scala3.std.*
import Formula.*
import Term.*

/**
 * A LIBRARY OF LEMMAS for a kernel: general theorems — closed, quantified — PROVED by the kernel (the arithmetic ones
 * by `Linarith`'s certificates, the rest by natural deduction), not assumed: the trusted base does not grow. Each is
 * proved once, when first asked for, and kept. Over `Int` and `Dec` the order and addition; for any sort equality;
 * for any formulas the classical schemas. Use one by `∀`-elimination (`Infer.allE`, `Rule.AllE`), or as a theorem
 * given to `Linarith.decide`.
 */
final class Lemmas(val kernel: Kernel):
  private val kept = mutable.Map.empty[(String, Any), Thm]

  private def keep(name: String, key: Any)(proof: => Thm ! Infer): Thm =
    kept.getOrElseUpdate((name, key),
      run(Infer.by(kernel)(proof)).fold(e => throw IllegalStateException(s"$name: $e"), identity))

  private def vars(s: Sort, names: String*): List[V] = names.toList.map(V(_, s))

  /** `∀x̄. h₁ ∧ … ∧ hₙ → c` (`∀x̄. c` with no hypotheses), `c` by linear arithmetic from the hypotheses */
  private def arith(name: String, s: Sort, xs: List[V], hyps: List[Formula], c: Formula): Thm = keep(name, s) {
    val body: Thm ! Infer = hyps match
      case Nil => Linarith.prove[Infer](c, Nil).getOrElse(Infer.refuse[Infer](s"$name: no certificate"))
      case _ =>
        val h = hyps.reduceLeft(And(_, _))
        Infer.assume[Infer](h).flatMap { t =>
          conjuncts[Infer](t, hyps.length).flatMap { parts =>
            Linarith.prove[Infer](c, Nil, parts).getOrElse(Infer.refuse[Infer](s"$name: no certificate"))
              .flatMap(r => Infer.impI[Infer](h, r))
          }
        }
    xs.foldRight(body)((x, p) => p.flatMap(t => Infer.allI[Infer](x, t)))
  }

  /** the n conjuncts of a left-nested conjunction's theorem */
  private def conjuncts[R[_]: Has[Infer]](t: Thm, n: Int): List[Thm] ! R =
    if n <= 1 then pure(List(t))
    else for
      l <- Infer.step[R](Rule.AndE1(t))
      r <- Infer.step[R](Rule.AndE2(t))
      ls <- conjuncts[R](l, n - 1)
    yield ls :+ r

  private def num(s: Sort): Unit = require(s == Sort.Int || s == Sort.Dec, s"not a numeric sort: $s")
  private def add(s: Sort, a: Term, b: Term): Term = Ap(if s == Sort.Int then Fns.add else Fns.dadd, List(a, b))
  private def sub(s: Sort, a: Term, b: Term): Term = Ap(if s == Sort.Int then Fns.sub else Fns.dsub, List(a, b))
  private def zero(s: Sort): Term = if s == Sort.Int then I(0) else D(BigDecimal(0))

  // -- ORDER (Int, Dec)

  /** `∀x. x ≤ x` */
  def leRefl(s: Sort): Thm = { num(s); val List(x) = vars(s, "x"): @unchecked; arith("leRefl", s, List(x), Nil, Le(x,
    x)) }
  /** `∀x y z. x ≤ y ∧ y ≤ z → x ≤ z` */
  def leTrans(s: Sort): Thm =
    num(s); val List(x, y, z) = vars(s, "x", "y", "z"): @unchecked
    arith("leTrans", s, List(x, y, z), List(Le(x, y), Le(y, z)), Le(x, z))
  /** `∀x y z. x < y ∧ y ≤ z → x < z` */
  def ltLeTrans(s: Sort): Thm =
    num(s); val List(x, y, z) = vars(s, "x", "y", "z"): @unchecked
    arith("ltLeTrans", s, List(x, y, z), List(Lt(x, y), Le(y, z)), Lt(x, z))
  /** `∀x y z. x ≤ y ∧ y < z → x < z` */
  def leLtTrans(s: Sort): Thm =
    num(s); val List(x, y, z) = vars(s, "x", "y", "z"): @unchecked
    arith("leLtTrans", s, List(x, y, z), List(Le(x, y), Lt(y, z)), Lt(x, z))
  /** `∀x. ¬(x < x)` */
  def ltIrrefl(s: Sort): Thm = { num(s); val List(x) = vars(s, "x"): @unchecked; arith("ltIrrefl", s, List(x), Nil,
    Not(Lt(x, x))) }
  /** `∀x y. x < y → x ≤ y` */
  def ltToLe(s: Sort): Thm =
    num(s); val List(x, y) = vars(s, "x", "y"): @unchecked
    arith("ltToLe", s, List(x, y), List(Lt(x, y)), Le(x, y))
  /** `∀x y. x ≤ y ∧ y ≤ x → x = y` */
  def leAntisym(s: Sort): Thm =
    num(s); val List(x, y) = vars(s, "x", "y"): @unchecked
    arith("leAntisym", s, List(x, y), List(Le(x, y), Le(y, x)), Eq(x, y))
  /** `∀x y. ¬(x ≤ y) → y < x` */
  def notLe(s: Sort): Thm =
    num(s); val List(x, y) = vars(s, "x", "y"): @unchecked
    arith("notLe", s, List(x, y), List(Not(Le(x, y))), Lt(y, x))
  /** `∀x y. ¬(x < y) → y ≤ x` */
  def notLt(s: Sort): Thm =
    num(s); val List(x, y) = vars(s, "x", "y"): @unchecked
    arith("notLt", s, List(x, y), List(Not(Lt(x, y))), Le(y, x))
  /** `∀x y. x ≤ y ∨ y ≤ x` — by cases on `x ≤ y` */
  def leTotal(s: Sort): Thm = keep("leTotal", s) {
    num(s); val List(x, y) = vars(s, "x", "y"): @unchecked
    val p = Le(x, y)
    val goal = Or(p, Le(y, x))
    for
      em <- excludedMiddleP[Infer](p)
      yes <- Infer.assume[Infer](p).flatMap(t => Infer.step[Infer](Rule.OrI1(t, Le(y, x))))
      no <- Linarith.prove[Infer](Le(y, x), List(Not(p))).get.flatMap(t => Infer.step[Infer](Rule.OrI2(p, t)))
      both <- Infer.step[Infer](Rule.OrE(em, yes, no))
      t1 <- Infer.allI[Infer](y, both)
      t <- Infer.allI[Infer](x, t1)
    yield { assert(both.concl == goal); t }
  }

  // -- ADDITION (Int, Dec)

  /** `∀x y. x + y = y + x` */
  def addComm(s: Sort): Thm =
    num(s); val List(x, y) = vars(s, "x", "y"): @unchecked
    arith("addComm", s, List(x, y), Nil, Eq(add(s, x, y), add(s, y, x)))
  /** `∀x y z. (x + y) + z = x + (y + z)` */
  def addAssoc(s: Sort): Thm =
    num(s); val List(x, y, z) = vars(s, "x", "y", "z"): @unchecked
    arith("addAssoc", s, List(x, y, z), Nil, Eq(add(s, add(s, x, y), z), add(s, x, add(s, y, z))))
  /** `∀x. x + 0 = x` */
  def addZero(s: Sort): Thm = { num(s); val List(x) = vars(s, "x"): @unchecked; arith("addZero", s, List(x), Nil,
    Eq(add(s, x, zero(s)), x)) }
  /** `∀x. x - x = 0` */
  def subSelf(s: Sort): Thm = { num(s); val List(x) = vars(s, "x"): @unchecked; arith("subSelf", s, List(x), Nil,
    Eq(sub(s, x, x), zero(s))) }
  /** `∀a b c d. a ≤ b ∧ c ≤ d → a + c ≤ b + d` */
  def addLeAdd(s: Sort): Thm =
    num(s); val List(a, b, c, d) = vars(s, "a", "b", "c", "d"): @unchecked
    arith("addLeAdd", s, List(a, b, c, d), List(Le(a, b), Le(c, d)), Le(add(s, a, c), add(s, b, d)))
  /** `∀a b. 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b` */
  def addNonneg(s: Sort): Thm =
    num(s); val List(a, b) = vars(s, "a", "b"): @unchecked
    arith("addNonneg", s, List(a, b), List(Le(zero(s), a), Le(zero(s), b)), Le(zero(s), add(s, a, b)))
  /** `∀a b. a ≤ b ↔ 0 ≤ b - a`, one way: `a ≤ b → 0 ≤ b - a` */
  def subNonneg(s: Sort): Thm =
    num(s); val List(a, b) = vars(s, "a", "b"): @unchecked
    arith("subNonneg", s, List(a, b), List(Le(a, b)), Le(zero(s), sub(s, b, a)))

  // -- THE INTEGERS

  /** `∀x y. x < y → x + 1 ≤ y` */
  def ltSuccLe: Thm =
    val List(x, y) = vars(Sort.Int, "x", "y"): @unchecked
    arith("ltSuccLe", Sort.Int, List(x, y), List(Lt(x, y)), Le(add(Sort.Int, x, I(1)), y))
  /** `∀x y. x < y + 1 → x ≤ y` */
  def leOfLtSucc: Thm =
    val List(x, y) = vars(Sort.Int, "x", "y"): @unchecked
    arith("leOfLtSucc", Sort.Int, List(x, y), List(Lt(x, add(Sort.Int, y, I(1)))), Le(x, y))

  // -- EQUALITY (any sort)

  /** `∀x. x = x` */
  def eqRefl(s: Sort): Thm = keep("eqRefl", s) {
    val x = V("x", s)
    Infer.refl[Infer](x).flatMap(t => Infer.allI[Infer](x, t))
  }
  /** `∀x y. x = y → y = x` */
  def eqSym(s: Sort): Thm = keep("eqSym", s) {
    val List(x, y, z) = vars(s, "x", "y", "z"): @unchecked
    for
      e <- Infer.assume[Infer](Eq(x, y))
      self <- Infer.refl[Infer](x)
      back <- Infer.subst[Infer](e, z, Eq(z, x), self)
      i <- Infer.impI[Infer](Eq(x, y), back)
      t1 <- Infer.allI[Infer](y, i)
      t <- Infer.allI[Infer](x, t1)
    yield t
  }
  /** `∀x y z. x = y ∧ y = z → x = z` */
  def eqTrans(s: Sort): Thm = keep("eqTrans", s) {
    val List(x, y, z, w) = vars(s, "x", "y", "z", "w"): @unchecked
    val h = And(Eq(x, y), Eq(y, z))
    for
      both <- Infer.assume[Infer](h)
      xy <- Infer.step[Infer](Rule.AndE1(both))
      yz <- Infer.step[Infer](Rule.AndE2(both))
      xz <- Infer.subst[Infer](yz, w, Eq(x, w), xy)
      i <- Infer.impI[Infer](h, xz)
      t2 <- Infer.allI[Infer](z, i)
      t1 <- Infer.allI[Infer](y, t2)
      t <- Infer.allI[Infer](x, t1)
    yield t
  }

  // -- CLASSICAL SCHEMAS (any formulas)

  /** `⊢ f ∨ ¬f` */
  def excludedMiddle(f: Formula): Thm = keep("excludedMiddle", f)(excludedMiddleP[Infer](f))

  private def excludedMiddleP[R[_]: Has[Infer]](f: Formula): Thm ! R = Infer.cases[R](f)

  /** `⊢ (f → g) → (¬g → ¬f)` */
  def contrapositive(f: Formula, g: Formula): Thm = keep("contrapositive", (f, g)) {
    for
      imp <- Infer.assume[Infer](Imp(f, g))
      notG <- Infer.assume[Infer](Not(g))
      fh <- Infer.assume[Infer](f)
      gh <- Infer.impE[Infer](imp, fh)
      c <- Infer.step[Infer](Rule.NotE(notG, gh))
      notF <- Infer.step[Infer](Rule.NotI(f, c))
      i1 <- Infer.impI[Infer](Not(g), notF)
      t <- Infer.impI[Infer](Imp(f, g), i1)
    yield t
  }

  /** `⊢ ¬(f ∧ g) → ¬f ∨ ¬g` */
  def deMorganAnd(f: Formula, g: Formula): Thm = keep("deMorganAnd", (f, g)) {
    val goal = Or(Not(f), Not(g))
    for
      notBoth <- Infer.assume[Infer](Not(And(f, g)))
      emF <- excludedMiddleP[Infer](f)
      // f: then ¬g, else ¬f
      fh <- Infer.assume[Infer](f)
      gh <- Infer.assume[Infer](g)
      both <- Infer.andI[Infer](fh, gh)
      c <- Infer.step[Infer](Rule.NotE(notBoth, both))
      notG <- Infer.step[Infer](Rule.NotI(g, c))
      whenF <- Infer.step[Infer](Rule.OrI2(Not(f), notG))
      nf <- Infer.assume[Infer](Not(f))
      whenNotF <- Infer.step[Infer](Rule.OrI1(nf, Not(g)))
      cases <- Infer.step[Infer](Rule.OrE(emF, whenF, whenNotF))
      t <- Infer.impI[Infer](Not(And(f, g)), cases)
    yield { assert(cases.concl == goal); t }
  }

  /** `⊢ ¬(f ∨ g) → ¬f ∧ ¬g` */
  def deMorganOr(f: Formula, g: Formula): Thm = keep("deMorganOr", (f, g)) {
    for
      notEither <- Infer.assume[Infer](Not(Or(f, g)))
      fh <- Infer.assume[Infer](f)
      l <- Infer.step[Infer](Rule.OrI1(fh, g))
      c1 <- Infer.step[Infer](Rule.NotE(notEither, l))
      notF <- Infer.step[Infer](Rule.NotI(f, c1))
      gh <- Infer.assume[Infer](g)
      r <- Infer.step[Infer](Rule.OrI2(f, gh))
      c2 <- Infer.step[Infer](Rule.NotE(notEither, r))
      notG <- Infer.step[Infer](Rule.NotI(g, c2))
      both <- Infer.andI[Infer](notF, notG)
      t <- Infer.impI[Infer](Not(Or(f, g)), both)
    yield t
  }

  /** every arithmetic lemma for `Int` and `Dec`, and the integers' — proved now */
  def all: List[(String, Thm)] =
    val sorts = List(Sort.Int, Sort.Dec)
    sorts.flatMap(s => List(
      s"leRefl $s" -> leRefl(s), s"leTrans $s" -> leTrans(s), s"ltLeTrans $s" -> ltLeTrans(s),
      s"leLtTrans $s" -> leLtTrans(s), s"ltIrrefl $s" -> ltIrrefl(s), s"ltToLe $s" -> ltToLe(s),
      s"leAntisym $s" -> leAntisym(s), s"notLe $s" -> notLe(s), s"notLt $s" -> notLt(s), s"leTotal $s" -> leTotal(s),
      s"addComm $s" -> addComm(s), s"addAssoc $s" -> addAssoc(s), s"addZero $s" -> addZero(s),
      s"subSelf $s" -> subSelf(s), s"addLeAdd $s" -> addLeAdd(s), s"addNonneg $s" -> addNonneg(s),
      s"subNonneg $s" -> subNonneg(s), s"eqRefl $s" -> eqRefl(s), s"eqSym $s" -> eqSym(s),
      s"eqTrans $s" -> eqTrans(s))) ++ List("ltSuccLe" -> ltSuccLe, "leOfLtSucc" -> leOfLtSucc)
