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

  // LINEAR ARITHMETIC, by certificate: a decision procedure outside the kernel finds the certificate, these check it

  /** `a = b`, `a ≤ b` or `a < b` (over `Int` or `Dec`) whose sides' linear forms differ by a constant of the right
   * sign: an identity of linear arithmetic, in one step — `x + y = y + x`, `x ≤ x + 1` */
  case Norm(f: Formula)
  /** premises read as `0 ≤ F`, `0 < F`, `0 = F` (`Linear.comparison`: `≤ < =` and the negated `≤ <`), each times its
   * coefficient — `≥ 0` for an inequality, any for an equation, an integer over `Int` — summed: `0 ≤ ΣλF`, or
   * `0 < ΣλF` if a strict one counts. With a constant sum of the wrong sign this is a contradiction: Farkas' */
  case LinComb(premises: List[(Thm, BigDecimal)])
  /** `a ≤ b` and `b ≤ a`: `a = b` */
  case Antisym(le: Thm, ge: Thm)
  /** over `Int`, `0 ≤ F` (`F` of integer coefficients): `0 ≤ F/g`, `g` their gcd, the constant rounded down — what
   * the integers have and the rationals not */
  case Tighten(t: Thm)
  /** premises read as `0 ≤ F` (`<`, `=`) and `0 ≤ G`: `0 ≤ F·G` — `0 < F·G` if both strict, `0 = F·G` if one is an
   * equation: the products of an ordered ring */
  case MulNonneg(a: Thm, b: Thm)
  /** `0 ≤ t·t` */
  case Square(t: Term)

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
    case Norm(f) =>
      import Linear.Kind
      val shape = f match
        case _: Eq | _: Le | _: Lt => true
        case _ => false
      need(shape && wellSorted(f), s"not a comparison: $f")(Linear.comparison(f) match
        case Some((d, k, _)) if d.isConst =>
          val c = d.const.signum
          val holds = k match
            case Kind.Equal => c == 0
            case Kind.NonStrict => c >= 0
            case Kind.Strict => c > 0
          need(holds, s"the sides differ by ${d.const}: $f is false")(thm(Set.empty, f, r))
        case Some(_) => Left(s"the sides differ by more than a constant: $f")
        case None => Left(s"not a comparison over Int or Dec: $f"))
    case LinComb(ps) => linComb(r, ps)
    case MulNonneg(a, b) => need(ours(a, b), Kernel.foreign)((Linear.comparison(a.concl), Linear.comparison(b.concl)) match
      case (Some((f, k1, s1)), Some((g, k2, s2))) if s1 == s2 =>
        import Linear.Kind
        val p = Linear.term(Linear.times(f, g, s1), s1)
        val c =
          if k1 == Kind.Equal || k2 == Kind.Equal then Eq(zero(s1), p)
          else if k1 == Kind.Strict && k2 == Kind.Strict then Lt(zero(s1), p)
          else Le(zero(s1), p)
        thm(a.hyps ++ b.hyps, c, r)
      case _ => Left(s"not two comparisons of one sort, Int or Dec: ${a.concl}; ${b.concl}"))
    case Square(t) => sortOf(t) match
      case Some(s) if s == Sort.Int || s == Sort.Dec =>
        Linear.lin(t) match
          case Some(f) => thm(Set.empty, Le(zero(s), Linear.term(Linear.times(f, f, s), s)), r)
          case None => Left(s"not a numeric term: $t")
      case _ => Left(s"not a numeric term: $t")
    case Antisym(le, ge) => need(ours(le, ge), Kernel.foreign)((le.concl, ge.concl) match
      case (Le(a, b), Le(b2, a2)) if a == a2 && b == b2 && sortOf(a).exists(s => s == Sort.Int || s == Sort.Dec) =>
        thm(le.hyps ++ ge.hyps, Eq(a, b), r)
      case (x, y) => Left(s"not a ≤ b and b ≤ a: $x; $y"))
    case Tighten(t) => need(ours(t), Kernel.foreign)(Linear.comparison(t.concl) match
      case Some((d, Linear.Kind.NonStrict, Sort.Int)) if !d.isConst && Linear.integral(d) =>
        val g = java.math.BigDecimal(Linear.gcd(d))
        val c = d.const.divide(g, 0, java.math.RoundingMode.FLOOR)
        val scaled = Lin(d.coeffs.view.mapValues(_.divide(g)).toMap, c)
        thm(t.hyps, Le(Term.I(0), Linear.term(scaled, Sort.Int)), r)
      case _ => Left(s"not 0 ≤ F over Int, F of integer coefficients and an atom: ${t.concl}"))

  private def zero(s: Sort): Term = if s == Sort.Int then Term.I(0) else Term.D(BigDecimal(0))

  private def linComb(r: Rule, ps: List[(Thm, BigDecimal)]): Either[String, Thm] =
    import Linear.Kind
    val read = ps.map((t, c) => (t, c.bigDecimal, Linear.comparison(t.concl)))
    read.collectFirst { case (t, _, None) => t } match
      case Some(t) => Left(s"not a linear comparison over Int or Dec: ${t.concl}")
      case None =>
        val rows = read.map { case (t, c, Some((f, k, s))) => (t, c, f, k, s); case _ => sys.error("unreachable") }
        val sorts = rows.map(_._5).distinct
        if ps.isEmpty then Left("no premises")
        else if !ours(ps.map(_._1)*) then Left(Kernel.foreign)
        else if sorts.length != 1 then Left(s"premises of two sorts: ${sorts.mkString(", ")}")
        else
          val s = sorts.head
          rows.collectFirst {
            case (t, c, _, k, _) if k != Kind.Equal && c.signum < 0 => s"a negative coefficient $c for ${t.concl}"
            case (t, c, _, _, _) if s == Sort.Int && c.stripTrailingZeros.scale > 0 => s"over Int, $c is not an integer"
          } match
            case Some(why) => Left(why)
            case None =>
              val total = rows.foldLeft(Lin.zero)((acc, r) => acc + r._3 * r._2)
              val strict = rows.exists(r => r._4 == Kind.Strict && r._2.signum > 0)
              val t = Linear.term(total, s)
              thm(rows.foldLeft(Set.empty[Formula])(_ ++ _._1.hyps),
                if strict then Lt(zero(s), t) else Le(zero(s), t), r)

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
  /** the first `n` characters (code points, as Lean's), all if fewer, none if `n` < 0 */
  val take = Fn("take", List(Str, Int), Str)
  /** the last `n` characters, likewise */
  val takeRight = Fn("takeRight", List(Str, Int), Str)
  /** where `p` first stands in `a`, in characters from 0; -1 if nowhere; 0 for the empty text */
  val indexOf = Fn("indexOf", List(Str, Str), Int)
  val all: Set[Fn] = Set(add, sub, mul, neg, div, mod, dec, dadd, dsub, dmul, ddiv, round, roundHalfUp, concat, length,
    take, takeRight, indexOf)

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
    case ("take", List(a: String, n: BigInt)) =>
      val cs = codePoints(a)
      Some(text(cs.take(n.max(0).min(cs.length).toInt)))
    case ("takeRight", List(a: String, n: BigInt)) =>
      val cs = codePoints(a)
      Some(text(cs.drop(cs.length - n.max(0).min(cs.length).toInt)))
    case ("indexOf", List(a: String, p: String)) => Some(BigInt(codePoints(a).indexOfSlice(codePoints(p))))
    case _ => None

  /** a text's characters: its code points, as Lean reads a string */
  private def codePoints(a: String): Vector[Int] =
    val b = Vector.newBuilder[Int]
    var i = 0
    while i < a.length do
      val c = a.codePointAt(i)
      b += c
      i += Character.charCount(c)
    b.result()

  private def text(cs: Seq[Int]): String =
    val b = java.lang.StringBuilder()
    cs.foreach(c => b.append(Character.toChars(c)))
    b.toString

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
