package okay.proof

import java.math.{BigDecimal as JDec, BigInteger}

/**
 * LINEAR FORMS — part of the trusted base, with the rules that use them (`Norm`, `LinComb`, `Tighten`): a term of
 * sort `Int` or `Dec` read as `Σ cᵢ·aᵢ + c`, its ATOMS `aᵢ` the terms that are not linear structure (variables,
 * functions of one's own, products of two non-constants, `div`, `round` of a non-constant …). Only identities true of
 * the integers and the rationals are used: `+`, `-`, `neg`, a product by a constant, a closed computable term its
 * value. An atom's arguments of sort `Int` or `Dec` are put in canonical form first, so `f(1 + x)` and `f(x + 1)` are
 * one atom — sound, a function giving equal values for equal arguments.
 */
final case class Lin(coeffs: Map[Term, JDec], const: JDec):
  def +(o: Lin): Lin = Lin(Lin.merge(coeffs, o.coeffs, JDec.ONE), const.add(o.const))
  def -(o: Lin): Lin = Lin(Lin.merge(coeffs, o.coeffs, JDec.ONE.negate), const.subtract(o.const))
  def *(c: JDec): Lin =
    if c.signum == 0 then Lin.zero else Lin(coeffs.view.mapValues(_.multiply(c)).toMap, const.multiply(c))
  def isConst: Boolean = coeffs.isEmpty

object Lin:
  val zero: Lin = Lin(Map.empty, JDec.ZERO)
  def const(c: JDec): Lin = Lin(Map.empty, c)
  def atom(t: Term): Lin = Lin(Map(t -> JDec.ONE), JDec.ZERO)

  private[proof] def merge(a: Map[Term, JDec], b: Map[Term, JDec], k: JDec): Map[Term, JDec] =
    b.foldLeft(a) { case (m, (t, c)) =>
      val v = m.getOrElse(t, JDec.ZERO).add(c.multiply(k))
      if v.signum == 0 then m - t else m.updated(t, v)
    }

object Linear:
  import Term.*

  private def isInt(s: Sort) = s == Sort.Int
  private def numeric(s: Sort) = s == Sort.Int || s == Sort.Dec

  /** `t`, of sort `Int` or `Dec`, as a linear form */
  def lin(t: Term): Option[Lin] = Logic.sortOf(t).filter(numeric).map(s => form(t, s))

  private def form(t: Term, s: Sort): Lin =
    if t.free.isEmpty then
      Arithmetic.value(t) match
        case Some(v: BigInt) => return Lin.const(JDec(v.bigInteger))
        case Some(v: JDec) => return Lin.const(v)
        case _ => ()
    t match
      case I(v) => Lin.const(JDec(v.bigInteger))
      case D(v) => Lin.const(v.bigDecimal)
      case Ap(fn, List(a, b)) if fn == Fns.add || fn == Fns.dadd => form(a, s) + form(b, s)
      case Ap(fn, List(a, b)) if fn == Fns.sub || fn == Fns.dsub => form(a, s) - form(b, s)
      case Ap(fn, List(a)) if fn == Fns.neg => form(a, s) * JDec.ONE.negate
      case Ap(fn, List(a, b)) if fn == Fns.mul || fn == Fns.dmul =>
        val (x, y) = (form(a, s), form(b, s))
        if x.isConst then y * x.const
        else if y.isConst then x * y.const
        else Lin.atom(canonical(t))
      case _ => Lin.atom(canonical(t))

  /** an atom with its numeric arguments in canonical form */
  private def canonical(t: Term): Term = t match
    case Ap(fn, as) => Ap(fn, as.map(a => Logic.sortOf(a) match
      case Some(s) if numeric(s) => term(form(a, s), s)
      case _ => canonical(a)))
    case other => other

  /** a linear form as a term of sort `s`: its atoms in a fixed order, then its constant */
  def term(l: Lin, s: Sort): Term =
    val one = JDec.ONE
    def lit(c: JDec): Term = if isInt(s) then I(BigInt(c.toBigIntegerExact)) else D(BigDecimal(c))
    val add = if isInt(s) then Fns.add else Fns.dadd
    val mul = if isInt(s) then Fns.mul else Fns.dmul
    val parts = l.coeffs.toList.sortBy(_._1.toString).map { (a, c) =>
      if c.compareTo(one) == 0 then a else Ap(mul, List(lit(c), a))
    }
    val all = if l.const.signum != 0 || parts.isEmpty then parts :+ lit(l.const) else parts
    all.reduceLeft((x, y) => Ap(add, List(x, y)))

  /** every coefficient and the constant integers */
  def integral(l: Lin): Boolean =
    def int(c: JDec) = c.signum == 0 || c.stripTrailingZeros.scale <= 0
    int(l.const) && l.coeffs.values.forall(int)

  /** the greatest common divisor of the coefficients (integers, not all zero) */
  def gcd(l: Lin): BigInteger =
    l.coeffs.values.foldLeft(BigInteger.ZERO)((g, c) => g.gcd(c.toBigIntegerExact.abs))

  /** a comparison `0 ≤ F`, `0 < F` or `0 = F` that a formula says, `F` its form, the sort with it; for `Int` a strict
   * one made `0 ≤ F - 1`. `¬(a ≤ b)` is `a - b > 0`, `¬(a < b)` is `a - b ≥ 0`: the orders are total */
  enum Kind:
    case NonStrict, Strict, Equal

  def comparison(f: Formula): Option[(Lin, Kind, Sort)] =
    import Formula.*
    def mk(a: Term, b: Term, k: Kind): Option[(Lin, Kind, Sort)] =
      for
        s <- Logic.sortOf(a).filter(numeric)
        if Logic.sortOf(b).contains(s)
      yield
        val d = form(b, s) - form(a, s)
        if k == Kind.Strict && isInt(s) then (d - Lin.const(JDec.ONE), Kind.NonStrict, s) else (d, k, s)
    f match
      case Le(a, b) => mk(a, b, Kind.NonStrict)
      case Lt(a, b) => mk(a, b, Kind.Strict)
      case Eq(a, b) => mk(a, b, Kind.Equal)
      case Not(Le(a, b)) => mk(b, a, Kind.Strict)
      case Not(Lt(a, b)) => mk(b, a, Kind.NonStrict)
      case _ => None
