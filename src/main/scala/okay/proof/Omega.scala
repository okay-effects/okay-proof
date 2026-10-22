package okay.proof

import java.math.{BigDecimal as JDec, BigInteger, RoundingMode}
import java.util.IdentityHashMap
import scala.collection.mutable
import okay.effects.*
import Formula.*
import Term.*

/**
 * THE OMEGA TEST (Pugh, 1991) — a COMPLETE decision of a conjunction of linear constraints over the integers, with
 * its refutation as steps the kernel checks; trusted for nothing, needing no rule beyond the ones there are:
 *
 *  - every row `0 ≤ F` tightened by the gcd of its coefficients (`Tighten`); an equation a pair of opposite rows;
 *  - an EQUATION with a coefficient ±1 solves its variable, substituted away by `LinComb`; with none, Pugh's `mod̂`:
 *    a fresh `σ` with `σ = Q` (`Q` linear, integral) gives an equation with a coefficient ±1 — `σ` introduced by
 *    `∃σ. σ = Q` and discharged by `ExE`;
 *  - an INEQUALITY's variable eliminated exactly (Fourier–Motzkin) when a side's coefficients are 1; otherwise the
 *    real shadow tried, then, for each pair of a lower bound `a·x ≥ α` and an upper `b·x ≤ β`, a case split: the
 *    DARK shadow `aβ − bα ≥ (a−1)(b−1)`, or not — and then `a·x − α ≤ ⌊((a−1)(b−1)−1)/b⌋`, the GREY shadow's
 *    splinters `a·x − α = i` each a case. Every split is `f ∨ ¬f` (`Infer.cases`) and `OrE`.
 *
 * Complete: if the constraints have no integer solution every branch ends in a false constant — the dark shadow
 * having a solution would give one. Within a budget of steps of the search, which a hard problem can exhaust.
 */
object Omega:
  /** where a row comes from: a premise (a fact, a case's hypothesis), a theorem given, a tightened sum */
  private sealed trait Node
  private final case class Fact(f: Formula) extends Node
  private final case class Given(t: Thm) extends Node
  private final class Tight(val prov: Map[Node, JDec]) extends Node

  /** `0 ≤ form`: the sum of nodes' comparisons times their multipliers */
  private final case class Row(form: Lin, prov: Map[Node, JDec])

  private enum Ref:
    /** a row whose form is a negative constant */
    case Contra(row: Row)
    case Split(f: Formula, yes: Ref, no: Ref)
    /** `σ = q` assumed in `body`, `σ` fresh */
    case Exists(sigma: V, q: Term, body: Ref)

  /** a refutation found */
  final class Plan private[Omega] (private[Omega] val ref: Ref)

  private val one = JDec.ONE
  private def num(n: Long) = JDec.valueOf(n)

  /** a contradiction among `facts` and `theorems` over `Int`, if the search finds one within `budget` */
  def refute(facts: List[Formula], theorems: List[Thm], budget: Int = 20000): Option[Plan] =
    val names = (facts ++ theorems.map(_.concl)).flatMap(_.free.map(_.name)).toSet
    val start = facts.flatMap(f => rowsOf(Fact(f), f)) ++ theorems.flatMap(t => rowsOf(Given(t), t.concl))
    Search(budget, names).refute(start.toVector).map(Plan(_))

  /** a premise's rows: its comparison over `Int`, an equation as two */
  private def rowsOf(n: Node, f: Formula): List[Row] = Linear.comparison(f) match
    case Some((form, Linear.Kind.Equal, Sort.Int)) => List(Row(form, Map(n -> one)), Row(form * one.negate, Map(n -> one.negate)))
    case Some((form, _, Sort.Int)) => List(Row(form, Map(n -> one)))
    case _ => Nil

  private def plus(a: Row, la: JDec, b: Row, lb: JDec): Row =
    val prov = b.prov.foldLeft(a.prov.view.mapValues(_.multiply(la)).toMap) { case (m, (k, c)) =>
      val v = m.getOrElse(k, JDec.ZERO).add(c.multiply(lb))
      if v.signum == 0 then m - k else m.updated(k, v)
    }
    Row(a.form * la + b.form * lb, prov)

  private def coef(r: Row, x: Term): JDec = r.form.coeffs.getOrElse(x, JDec.ZERO)

  private def opposite(a: Lin, b: Lin): Boolean =
    a.coeffs.size == b.coeffs.size && a.const.add(b.const).signum == 0 &&
      a.coeffs.forall((k, c) => b.coeffs.get(k).exists(_.add(c).signum == 0))

  private def floorDiv(a: JDec, b: JDec): JDec = a.divide(b, 0, RoundingMode.FLOOR)

  /** Pugh's symmetric residue: `v − m·⌊v/m + 1/2⌋` */
  private def modHat(v: BigInteger, m: BigInteger): BigInteger =
    val two = BigInteger.TWO
    val q = floorDivI(v.multiply(two).add(m), m.multiply(two))
    v.subtract(m.multiply(q))

  private def floorDivI(a: BigInteger, b: BigInteger): BigInteger =
    val qr = a.divideAndRemainder(b)
    if qr(1).signum != 0 && (qr(1).signum != b.signum) then qr(0).subtract(BigInteger.ONE) else qr(0)

  private final class Search(var budget: Int, names: Set[String]):
    private var fresh = 0
    private val used = mutable.Set.from(names)

    private def sigma(): V =
      var v = V("σ", Sort.Int)
      while used.contains(v.name) do
        fresh += 1
        v = V(s"σ$fresh", Sort.Int)
      used += v.name
      v

    /** a row tightened: divided by the gcd of its coefficients, the constant rounded down (`Tighten`) */
    private def tighten(r: Row): Row =
      if r.form.isConst then r
      else
        val g = Linear.gcd(r.form)
        if g.compareTo(BigInteger.ONE) <= 0 then r
        else
          val gd = JDec(g)
          Row(Lin(r.form.coeffs.view.mapValues(_.divide(gd)).toMap, floorDiv(r.form.const, gd)), Map(Tight(r.prov) -> one))

    def refute(input: Vector[Row]): Option[Ref] =
      budget -= 1
      if budget <= 0 then return None
      val rows = input.map(tighten).filterNot(r => r.form.isConst && r.form.const.signum >= 0)
      rows.find(r => r.form.isConst) match
        case Some(r) => return Some(Ref.Contra(r))
        case None => ()
      equality(rows) match
        case Some((pos, neg)) => solve(rows, pos, neg)
        case None => inequalities(rows)

    /** a pair of opposite rows: an equation `0 = F`, a coefficient ±1 preferred */
    private def equality(rows: Vector[Row]): Option[(Row, Row)] =
      val pairs = for
        i <- rows.indices.iterator
        j <- (i + 1 until rows.length).iterator
        if opposite(rows(i).form, rows(j).form)
      yield (rows(i), rows(j))
      val all = pairs.toVector
      all.find((p, _) => p.form.coeffs.values.exists(_.abs.compareTo(one) == 0)).orElse(all.headOption)

    private def solve(rows: Vector[Row], pos: Row, neg: Row): Option[Ref] =
      pos.form.coeffs.find(_._2.abs.compareTo(one) == 0) match
        case Some((x, c)) =>
          // x solved by 0 = F, c = ±1: each other row r + λF with λ = −d·c, through pos (λ ≥ 0) or neg
          val rest = rows.filterNot(r => (r eq pos) || (r eq neg)).map { r =>
            val d = coef(r, x)
            if d.signum == 0 then r
            else
              val l = d.multiply(c).negate
              if l.signum > 0 then plus(r, one, pos, l) else plus(r, one, neg, l.negate)
          }
          refute(rest)
        case None =>
          // Pugh's mod̂: m = |c_k| + 1 for the least |c_k|; σ = Q, so that F + m(Q − σ) has a coefficient ∓1 on x_k
          val (xk, ck) = pos.form.coeffs.minBy(_._2.abs)
          val m = ck.toBigIntegerExact.abs.add(BigInteger.ONE)
          val md = JDec(m)
          def q(v: JDec): JDec = JDec(modHat(v.toBigIntegerExact, m).subtract(v.toBigIntegerExact)).divide(md)
          val qForm = Lin(pos.form.coeffs.view.mapValues(q).toMap.filter(_._2.signum != 0), q(pos.form.const))
          val s = sigma()
          val qTerm = Linear.term(qForm, Sort.Int)
          val h = Eq(s, qTerm)
          rowsOf(Fact(h), h) match
            case List(hp, hn) =>
              val newPos = plus(pos, one, hp, md)
              val newNeg = plus(neg, one, hn, md)
              refute(rows :+ newPos :+ newNeg).map(Ref.Exists(s, qTerm, _))
            case _ => None

    private def inequalities(rows: Vector[Row]): Option[Ref] =
      val atoms = rows.iterator.flatMap(_.form.coeffs.keysIterator).distinct.toVector
      if atoms.isEmpty then return None
      def lowers(x: Term) = rows.filter(coef(_, x).signum > 0)
      def uppers(x: Term) = rows.filter(coef(_, x).signum < 0)
      // a variable bounded on one side only: its rows can always be met — dropped
      atoms.find(x => lowers(x).isEmpty || uppers(x).isEmpty) match
        case Some(x) => return refute(rows.filter(coef(_, x).signum == 0))
        case None => ()
      def exact(x: Term) =
        lowers(x).forall(coef(_, x).compareTo(one) == 0) || uppers(x).forall(coef(_, x).compareTo(one.negate) == 0)
      def cost(x: Term) = lowers(x).length.toLong * uppers(x).length
      val x = atoms.filter(exact).minByOption(cost).getOrElse(atoms.minBy(cost))
      val (ls, us) = (lowers(x), uppers(x))
      val without = rows.filter(coef(_, x).signum == 0)
      val pairs = for l <- ls; u <- us yield (l, u)
      // the real shadow: b·l + a·u, x gone
      def shadow(l: Row, u: Row): Row = plus(l, coef(u, x).negate, u, coef(l, x))
      val real = without ++ pairs.map(shadow)
      if exact(x) then refute(real)
      else refute(real).orElse(darkOrGrey(rows, without, x, pairs.toList, Vector.empty))

    /** each pair, the dark shadow's case or the grey shadow's splinters */
    private def darkOrGrey(rows: Vector[Row], without: Vector[Row], x: Term, pairs: List[(Row, Row)],
        dark: Vector[Row]): Option[Ref] = pairs match
      case Nil => refute(without ++ dark)
      case (l, u) :: rest =>
        val a = coef(l, x)
        val b = coef(u, x).negate
        val combo = plus(l, b, u, a).form
        val d = a.subtract(one).multiply(b.subtract(one))
        val f = Le(I(BigInt(d.toBigIntegerExact)), Linear.term(combo, Sort.Int))
        for
          yes <- darkOrGrey(rows, without, x, rest, dark ++ rowsOf(Fact(f), f))
          no <- grey(rows ++ rowsOf(Fact(Not(f)), Not(f)), l, b, d)
        yield Ref.Split(f, yes, no)

    /** `0 ≤ t ≤ K`, `t = a·x − α` the lower bound's form, `K = ⌊((a−1)(b−1)−1)/b⌋`: a case for each value */
    private def grey(rows: Vector[Row], l: Row, b: JDec, d: JDec): Option[Ref] =
      val k = floorDiv(d.subtract(one), b)
      val t = Linear.term(l.form, Sort.Int)
      def splinter(i: JDec, rs: Vector[Row]): Option[Ref] =
        if i.compareTo(k) > 0 then refute(rs)
        else
          val f = Le(t, I(BigInt(i.toBigIntegerExact)))
          for
            yes <- refute(rs ++ rowsOf(Fact(f), f))
            no <- splinter(i.add(one), rs ++ rowsOf(Fact(Not(f)), Not(f)))
          yield Ref.Split(f, yes, no)
      splinter(JDec.ZERO, rows)

  /** the refutation as steps: `False`, its hypotheses the facts used */
  def emit[R[_]: Has[Infer]](plan: Plan): Thm ! R =
    val facts = mutable.Map.empty[Formula, Thm]
    val tights = IdentityHashMap[Tight, Thm]()
    def node(n: Node): Thm ! R = n match
      case Fact(f) => facts.get(f) match
        case Some(t) => pure(t)
        case None => Infer.assume[R](f).map { t => facts(f) = t; t }
      case Given(t) => pure(t)
      case t: Tight => Option(tights.get(t)) match
        case Some(done) => pure(done)
        case None => sum(t.prov).flatMap(c => Infer.step[R](Rule.Tighten(c))).map { r => tights.put(t, r); r }
    def sum(prov: Map[Node, JDec]): Thm ! R =
      prov.toList.foldLeft(pure[List[(Thm, BigDecimal)], R](Nil)) { case (acc, (n, c)) =>
        acc.flatMap(l => node(n).map(t => l :+ (t -> BigDecimal(c))))
      }.flatMap(ps => Infer.step[R](Rule.LinComb(ps)))
    def ref(r: Ref): Thm ! R = r match
      case Ref.Contra(row) =>
        sum(row.prov).flatMap { c =>
          val no = c.concl match
            case Le(z, k) => Not(Le(z, k))
            case Lt(z, k) => Not(Lt(z, k))
            case other => Not(other)
          Infer.compute[R](no).flatMap(n => Infer.step[R](Rule.NotE(n, c)))
        }
      case Ref.Split(f, yes, no) =>
        for
          em <- Infer.cases[R](f)
          y <- ref(yes)
          n <- ref(no)
          t <- Infer.step[R](Rule.OrE(em, y, n))
        yield t
      case Ref.Exists(s, q, body) =>
        for
          r <- Infer.refl[R](q)
          ex <- Infer.step[R](Rule.ExI(s, Eq(s, q), q, r))
          b <- ref(body)
          t <- Infer.step[R](Rule.ExE(ex, s, b))
        yield t
    ref(plan.ref)
