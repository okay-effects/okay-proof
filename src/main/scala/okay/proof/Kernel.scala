package okay.proof

import java.math.{BigDecimal as JDec, RoundingMode}

/**
 * ONE INFERENCE STEP, as data: the rule and what it is applied to. It is what a program asks the kernel for (the
 * effect `Infer`), what a theorem remembers it was made by (`Thm.by`), and a certificate's node.
 */
enum Rule:
  /** `{f} ⊢ f` */
  case Assume(f: Formula)
  /** `⊢ a`, the theory's axiom named `name` */
  case Axiom(name: String)
  /** `⊢ f`, `f` closed, of the kernel's own functions only, computed true — exact arithmetic, one step */
  case Compute(f: Formula)
  case AndI(a: Thm, b: Thm)
  case AndE1(t: Thm)
  case AndE2(t: Thm)
  case OrI1(t: Thm, right: Formula)
  case OrI2(left: Formula, t: Thm)
  /** from `a ∨ b`, a proof of `c` assuming `a` and one assuming `b`: `c` */
  case OrE(t: Thm, left: Thm, right: Thm)
  /** `f` discharged: `⊢ f → c` */
  case ImpI(f: Formula, t: Thm)
  case ImpE(imp: Thm, arg: Thm)
  /** `False` from `f`, `f` discharged: `⊢ ¬f` */
  case NotI(f: Formula, t: Thm)
  /** `¬f` and `f`: `⊢ False` */
  case NotE(not: Thm, t: Thm)
  /** `¬¬f`: `⊢ f` — the logic is classical */
  case Classic(t: Thm)
  case FalseE(t: Thm, f: Formula)
  /** `⊢ ∀x. c`, `x` free in no hypothesis */
  case AllI(x: Term.V, t: Thm)
  case AllE(t: Thm, by: Term)
  /** `⊢ f[by/x]`: `⊢ ∃x. f` */
  case ExI(x: Term.V, f: Formula, by: Term, t: Thm)
  /** from `∃x. f`, a proof of `c` assuming `f[y/x]`, `y` fresh: `c` */
  case ExE(ex: Thm, y: Term.V, t: Thm)
  case Refl(t: Term)
  /** `s = u` and `f[s/x]`: `f[u/x]` */
  case Subst(eq: Thm, x: Term.V, f: Formula, t: Thm)
  /** `f[0/x]` and `∀x. 0 ≤ x ∧ f → f[x+1/x]`: `∀x. 0 ≤ x → f` */
  case Induct(x: Term.V, f: Formula, base: Thm, step: Thm)

/** axioms by name, each closed and well-sorted: what a kernel takes as given — policies, definitions */
final class Theory private (val name: String, val axioms: Map[String, Formula]):
  def apply(n: String): Option[Formula] = axioms.get(n)
  /** this theory and that one's axioms: a name in both must be the same axiom */
  def ++(that: Theory): Theory = Theory(s"$name+${that.name}", (that.axioms ++ axioms).toList*)
  override def toString = s"Theory($name: ${axioms.size} axioms)"

object Theory:
  def apply(name: String, axioms: (String, Formula)*): Theory =
    val m = axioms.toMap
    require(m.size == axioms.size || axioms.groupBy(_._1).forall(_._2.map(_._2).distinct.size == 1),
      "an axiom's name given twice, to two formulas")
    for (n, f) <- m do
      require(f.free.isEmpty, s"axiom $n is not closed: ${f.free.mkString(", ")} free")
      require(Logic.wellSorted(f), s"axiom $n is not well-sorted: $f")
    new Theory(name, m)
  val empty: Theory = apply("empty")

/**
 * THE KERNEL of a theory: the only maker of theorems. Each rule a pure function of its premises, checked; a theorem
 * of another kernel is refused as a premise, so a theorem is always relative to the one theory it was made under
 * (`owns`). Soundness rests on this file and `Logic`, on `Thm`'s constructor being the kernel's alone,
 * and on `Arithmetic`, and on nothing else — not on who asked, nor on any handler the asking went through.
 */
final class Kernel(val theory: Theory):
  import Formula.*
  import Logic.*
  import Rule.*

  /** this kernel made `t` */
  def owns(t: Thm): Boolean = t.kernel eq this

  private def thm(hyps: Set[Formula], concl: Formula, by: Rule): Either[String, Thm] =
    Right(Kernel.make(this, hyps, concl, by))

  private inline def need(ok: Boolean, why: => String)(body: => Either[String, Thm]): Either[String, Thm] =
    if ok then body else Left(why)

  private def ours(ts: Thm*): Boolean = ts.forall(_.kernel eq this)

  /** one step, checked: the theorem, or why not */
  def derive(r: Rule): Either[String, Thm] = r match
    case Assume(f) => need(wellSorted(f), s"not well-sorted: $f")(thm(Set(f), f, r))
    case Axiom(n) => theory(n) match
      case Some(f) => thm(Set.empty, f, r)
      case None => Left(s"no axiom '$n' in ${theory.name}")
    case Compute(f) =>
      need(wellSorted(f) && f.free.isEmpty, s"not closed and well-sorted: $f") {
        Arithmetic.truth(f) match
          case Some(true) => thm(Set.empty, f, r)
          case Some(false) => Left(s"computed false: $f")
          case None => Left(s"not computable (a symbol of one's own, a quantifier, an undefined operation): $f")
      }
    case AndI(a, b) => need(ours(a, b), Kernel.foreign)(thm(a.hyps ++ b.hyps, And(a.concl, b.concl), r))
    case AndE1(t) => need(ours(t), Kernel.foreign)(t.concl match
      case And(a, _) => thm(t.hyps, a, r)
      case c => Left(s"not a conjunction: $c"))
    case AndE2(t) => need(ours(t), Kernel.foreign)(t.concl match
      case And(_, b) => thm(t.hyps, b, r)
      case c => Left(s"not a conjunction: $c"))
    case OrI1(t, right) => need(ours(t) && wellSorted(right), s"${Kernel.foreign}, or not well-sorted: $right")(
      thm(t.hyps, Or(t.concl, right), r))
    case OrI2(left, t) => need(ours(t) && wellSorted(left), s"${Kernel.foreign}, or not well-sorted: $left")(
      thm(t.hyps, Or(left, t.concl), r))
    case OrE(t, l, rt) => need(ours(t, l, rt), Kernel.foreign)(t.concl match
      case Or(a, b) => need(alphaEq(l.concl, rt.concl), s"two cases, two conclusions: ${l.concl}; ${rt.concl}")(
        thm(t.hyps ++ (l.hyps - a) ++ (rt.hyps - b), l.concl, r))
      case c => Left(s"not a disjunction: $c"))
    case ImpI(f, t) => need(ours(t) && wellSorted(f), s"${Kernel.foreign}, or not well-sorted: $f")(
      thm(t.hyps - f, Imp(f, t.concl), r))
    case ImpE(i, a) => need(ours(i, a), Kernel.foreign)(i.concl match
      case Imp(p, q) => need(alphaEq(p, a.concl), s"the premise ${a.concl} is not $p")(thm(i.hyps ++ a.hyps, q, r))
      case c => Left(s"not an implication: $c"))
    case NotI(f, t) => need(ours(t) && wellSorted(f) && t.concl == False, s"not False from $f: ${t.concl}")(
      thm(t.hyps - f, Not(f), r))
    case NotE(n, t) => need(ours(n, t), Kernel.foreign)(n.concl match
      case Not(p) => need(alphaEq(p, t.concl), s"${t.concl} is not $p")(thm(n.hyps ++ t.hyps, False, r))
      case c => Left(s"not a negation: $c"))
    case Classic(t) => need(ours(t), Kernel.foreign)(t.concl match
      case Not(Not(p)) => thm(t.hyps, p, r)
      case c => Left(s"not a double negation: $c"))
    case FalseE(t, f) => need(ours(t) && t.concl == False && wellSorted(f), s"not False: ${t.concl}")(
      thm(t.hyps, f, r))
    case AllI(x, t) => need(ours(t), Kernel.foreign)(
      need(!t.hyps.exists(_.free.contains(x)), s"$x is free in a hypothesis")(thm(t.hyps, All(x, t.concl), r)))
    case AllE(t, by) => need(ours(t), Kernel.foreign)(t.concl match
      case All(x, f) => need(sortOf(by).contains(x.sort), s"$by is not of $x's sort ${x.sort}")(
        thm(t.hyps, subst(f, x, by), r))
      case c => Left(s"not universal: $c"))
    case ExI(x, f, by, t) =>
      need(ours(t) && wellSorted(f) && sortOf(by).contains(x.sort), s"${Kernel.foreign}, or ill-sorted: $f, $by")(
        need(alphaEq(t.concl, subst(f, x, by)), s"${t.concl} is not ${subst(f, x, by)}")(thm(t.hyps, Ex(x, f), r)))
    case ExE(e, y, t) => need(ours(e, t), Kernel.foreign)(e.concl match
      case Ex(x, f) =>
        val inst = subst(f, x, y)
        val rest = t.hyps - inst
        need(y.sort == x.sort && !t.concl.free.contains(y) && !e.concl.free.contains(y)
          && !rest.exists(_.free.contains(y)) && !e.hyps.exists(_.free.contains(y)), s"$y is not fresh")(
          thm(e.hyps ++ rest, t.concl, r))
      case c => Left(s"not existential: $c"))
    case Refl(t) => need(sortOf(t).isDefined, s"not well-sorted: $t")(thm(Set.empty, Eq(t, t), r))
    case Subst(eq, x, f, t) => need(ours(eq, t) && wellSorted(f), s"${Kernel.foreign}, or not well-sorted: $f")(
      eq.concl match
        case Eq(s, u) => need(sortOf(s).contains(x.sort), s"$s is not of $x's sort")(
          need(alphaEq(t.concl, subst(f, x, s)), s"${t.concl} is not ${subst(f, x, s)}")(
            thm(eq.hyps ++ t.hyps, subst(f, x, u), r)))
        case c => Left(s"not an equation: $c"))
    case Induct(x, f, base, step) =>
      need(ours(base, step) && x.sort == Sort.Int && wellSorted(f), s"${Kernel.foreign}, or not over the integers")(
        need(alphaEq(base.concl, subst(f, x, Term.I(0))), s"the base ${base.concl} is not ${subst(f, x, Term.I(0))}") {
          val next = subst(f, x, Term.Ap(Fns.add, List(x, Term.I(1))))
          val want = All(x, Imp(And(Le(Term.I(0), x), f), next))
          need(alphaEq(step.concl, want), s"the step ${step.concl} is not $want")(
            thm(base.hyps ++ step.hyps, All(x, Imp(Le(Term.I(0), x), f)), r))
        })

object Kernel:
  /** a THEOREM: hypotheses ⊢ conclusion, made by its kernel alone (`by` the step that made it) */
  final class Thm private[Kernel] (val kernel: Kernel, val hyps: Set[Formula], val concl: Formula, val by: Rule):
    override def toString: String = (if hyps.isEmpty then "" else hyps.mkString(", ") + " ") + "⊢ " + concl

  private def make(k: Kernel, hyps: Set[Formula], concl: Formula, by: Rule): Thm = new Thm(k, hyps, concl, by)

  private val foreign = "a theorem of another kernel (another theory) used here"

/** the kernel's own functions: computed exactly — integers unbounded, decimals of any scale, rounding only where a
 * function says so, and how */
object Fns:
  import Sort.*
  val add = Fn("+", List(Int, Int), Int)
  val sub = Fn("-", List(Int, Int), Int)
  val mul = Fn("*", List(Int, Int), Int)
  val neg = Fn("neg", List(Int), Int)
  /** floor division, and its remainder: undefined by zero (never computed) */
  val div = Fn("div", List(Int, Int), Int)
  val mod = Fn("mod", List(Int, Int), Int)
  val dec = Fn("dec", List(Int), Dec)
  val dadd = Fn("d+", List(Dec, Dec), Dec)
  val dsub = Fn("d-", List(Dec, Dec), Dec)
  val dmul = Fn("d*", List(Dec, Dec), Dec)
  /** `a / b` to `scale` places, half to even */
  val ddiv = Fn("d/", List(Dec, Dec, Int), Dec)
  /** to `scale` places, half to even (banker's) */
  val round = Fn("round", List(Dec, Int), Dec)
  /** to `scale` places, half up */
  val roundHalfUp = Fn("roundHalfUp", List(Dec, Int), Dec)
  val concat = Fn("++", List(Str, Str), Str)
  val length = Fn("length", List(Str), Int)
  val all: Set[Fn] = Set(add, sub, mul, neg, div, mod, dec, dadd, dsub, dmul, ddiv, round, roundHalfUp, concat, length)

/** THE INTRINSIC ARITHMETIC: a closed formula of the kernel's own functions, evaluated; `None` where it cannot be —
 * a symbol of one's own, a quantifier, division by zero, a scale out of range */
object Arithmetic:
  import Formula.*
  import Term.*

  def value(t: Term): Option[Any] = t match
    case I(v) => Some(v)
    case D(v) => Some(v.bigDecimal)
    case S(v) => Some(v)
    case _: V => None
    case Ap(fn, as) =>
      if !Fns.all.contains(fn) then None
      else
        val vs = as.map(value)
        if vs.exists(_.isEmpty) then None else apply(fn, vs.map(_.get))

  private def scale(n: BigInt): Option[Int] = Option.when(n >= -1000 && n <= 1000)(n.toInt)

  private def apply(fn: Fn, vs: List[Any]): Option[Any] = (fn.name, vs) match
    case ("+", List(a: BigInt, b: BigInt)) => Some(a + b)
    case ("-", List(a: BigInt, b: BigInt)) => Some(a - b)
    case ("*", List(a: BigInt, b: BigInt)) => Some(a * b)
    case ("neg", List(a: BigInt)) => Some(-a)
    case ("div", List(a: BigInt, b: BigInt)) => Option.when(b != 0)(floorDiv(a, b))
    case ("mod", List(a: BigInt, b: BigInt)) => Option.when(b != 0)(a - b * floorDiv(a, b))
    case ("dec", List(a: BigInt)) => Some(JDec(a.bigInteger))
    case ("d+", List(a: JDec, b: JDec)) => Some(a.add(b))
    case ("d-", List(a: JDec, b: JDec)) => Some(a.subtract(b))
    case ("d*", List(a: JDec, b: JDec)) => Some(a.multiply(b))
    case ("d/", List(a: JDec, b: JDec, s: BigInt)) =>
      if b.signum == 0 then None else scale(s).map(a.divide(b, _, RoundingMode.HALF_EVEN))
    case ("round", List(a: JDec, s: BigInt)) => scale(s).map(a.setScale(_, RoundingMode.HALF_EVEN))
    case ("roundHalfUp", List(a: JDec, s: BigInt)) => scale(s).map(a.setScale(_, RoundingMode.HALF_UP))
    case ("++", List(a: String, b: String)) => Some(a + b)
    case ("length", List(a: String)) => Some(BigInt(a.codePointCount(0, a.length)))
    case _ => None

  private def floorDiv(a: BigInt, b: BigInt): BigInt =
    val (q, r) = a /% b
    if r != 0 && (r.signum != b.signum) then q - 1 else q

  private def compare(a: Any, b: Any): Option[Int] = (a, b) match
    case (x: BigInt, y: BigInt) => Some(x.compare(y))
    case (x: JDec, y: JDec) => Some(x.compareTo(y))
    case _ => None

  /** a closed, quantifier-free formula's truth, if computable */
  def truth(f: Formula): Option[Boolean] = f match
    case True => Some(true)
    case False => Some(false)
    case Eq(a, b) => for x <- value(a); y <- value(b) yield
      (x, y) match
        case (p: JDec, q: JDec) => p.compareTo(q) == 0
        case _ => x == y
    case Lt(a, b) => for x <- value(a); y <- value(b); c <- compare(x, y) yield c < 0
    case Le(a, b) => for x <- value(a); y <- value(b); c <- compare(x, y) yield c <= 0
    case Not(g) => truth(g).map(!_)
    case And(a, b) => truth(a).flatMap(x => if !x then Some(false) else truth(b))
    case Or(a, b) => truth(a).flatMap(x => if x then Some(true) else truth(b))
    case Imp(a, b) => truth(a).flatMap(x => if !x then Some(true) else truth(b))
    case _ => None
