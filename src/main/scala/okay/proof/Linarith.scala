package okay.proof

import java.math.{BigDecimal as JDec, BigInteger}
import scala.collection.mutable
import okay.effects.*
import Formula.*

/**
 * LINEAR ARITHMETIC, DECIDED — outside the kernel, trusted for nothing: it finds a certificate and the kernel checks
 * it. A comparison over `Int` or `Dec` (`≤ < =` or a negated `≤ <`) is proved from facts and theorems theorems by
 * refutation: its negation assumed, Fourier–Motzkin elimination finds non-negative multipliers of the premises whose
 * sum is a false constant (Farkas'), `LinComb` checks the sum, `Compute` its falsity, and the negation is discharged.
 * An equation is two inequalities and `Antisym`. Over `Int`, a strict comparison is `+ 1 ≤`, and a derived inequality
 * whose coefficients share a factor is tightened (`Tighten`: the constant rounded down); what that does not refute
 * goes to the OMEGA TEST, complete over the integers (`Omega`). Complete over the rationals (`Dec`) and the integers
 * for linear problems; for products of variables (a monomial one more variable to the elimination) sound, by the
 * premises' pairwise products and the atoms' squares (`refuteProducts`), not complete. Atoms are the terms that are not
 * ring structure: `limit(teller)`, `sum(x)`.
 */
object Linarith:
  import Linear.Kind

  /** where a row comes from: a fact (assumed), a theorem theorems, or a derived row tightened */
  private enum Leaf:
    case Fact(f: Formula)
    case Given(t: Thm)
    case Tight(prov: Map[Int, JDec])
    /** the product of two leaves' comparisons (`MulNonneg`) */
    case Prod(i: Int, j: Int)
    /** a square (`Square`) */
    case Sq(t: Term)

  /** `0 ≤ form` (`0 < form` if strict), as the sum of leaves times their multipliers */
  private final case class Row(form: Lin, strict: Boolean, prov: Map[Int, JDec])

  /** a refutation found: the leaves, and the row of a false constant */
  final class Plan private[Linarith] (private[Linarith] val leaves: Vector[Leaf], private[Linarith] val row: Row,
      private[Linarith] val sort: Sort)

  /** a contradiction among `facts` and `theorems` over `sort`, if one is found within `limit` rows */
  def refute(facts: List[Formula], theorems: List[Thm], sort: Sort, limit: Int = 4000): Option[Plan] =
    refuteFrom(facts.headOption, facts, theorems, sort, limit)

  /** the premises that can matter to `goal`: those connected to its atoms through shared atoms (all, if it has no
   * atom) — a fact about another account's limit makes rows, and never a contradiction with this goal. Incomplete
   * only where the facts contradict each other apart from the goal's atoms: such a contradiction is not used */
  private def relevant(goal: Option[Formula], cands: List[(Formula, Lin)]): Set[Formula] =
    def atomsOf(l: Lin): Set[Term] = l.coeffs.keySet.flatMap(Linear.factors)
    val start = goal.flatMap(Linear.comparison).map(c => atomsOf(c._1)).getOrElse(Set.empty)
    if start.isEmpty then cands.map(_._1).toSet
    else
      val g = goal.get
      var atoms = start
      var chosen = cands.filter(c => c._2.coeffs.isEmpty || c._1 == g).map(_._1).toSet
      var grew = true
      while grew do
        grew = false
        for (f, l) <- cands if !chosen.contains(f) && atomsOf(l).exists(atoms.contains) do
          chosen += f
          atoms ++= atomsOf(l)
          grew = true
      chosen

  /** the facts and theorems connected to `goal`'s atoms */
  private def select(goal: Formula, facts: List[Formula], theorems: List[Thm], sort: Sort): (List[Formula], List[Thm]) =
    val cands = (facts ++ theorems.map(_.concl)).flatMap(f => Linear.comparison(f).collect {
      case (l, _, s) if s == sort => f -> l
    })
    val keep = relevant(Some(goal), cands)
    (facts.filter(keep.contains), theorems.filter(t => keep.contains(t.concl)))

  /** `False` from `assumed` (the negated goal), the facts and the theorems: linear elimination over the rationals
   * (with the integers' tightening); over `Int` then the Omega test, complete; then products, for what is nonlinear */
  private def falsum[R[_]: Has[Infer]](assumed: Formula, facts: List[Formula], theorems: List[Thm], s: Sort)
      : Option[Thm ! R] =
    val (fs, ts) = select(assumed, assumed :: facts, theorems, s)
    // products only where there is a product: on a linear problem the steps before are complete
    def nonlinear = (fs ++ ts.map(_.concl)).exists(f =>
      Linear.comparison(f).exists(_._1.coeffs.keysIterator.exists(m => Linear.factors(m).length > 1)))
    refute(fs, ts, s).map(emit[R](_))
      .orElse(if s == Sort.Int then Omega.refute(fs, ts).map(Omega.emit[R](_)) else None)
      .orElse(if nonlinear then refuteProducts(fs, ts, s).map(emit[R](_)) else None)

  private def refuteFrom(goal: Option[Formula], facts: List[Formula], theorems: List[Thm], sort: Sort, limit: Int)
      : Option[Plan] =
    val cands = (facts ++ theorems.map(_.concl)).flatMap(f => Linear.comparison(f).collect {
      case (l, _, s) if s == sort => f -> l
    })
    val keep = relevant(goal, cands)
    val leaves = mutable.ArrayBuffer.empty[Leaf]
    val rows = mutable.ArrayBuffer.empty[Row]
    def add(leaf: Leaf, f: Formula): Unit = if keep.contains(f) then Linear.comparison(f) match
      case Some((form, kind, s)) if s == sort =>
        val i = leaves.length
        leaves += leaf
        kind match
          case Kind.Equal =>
            rows += Row(form, false, Map(i -> JDec.ONE))
            rows += Row(form * JDec.ONE.negate, false, Map(i -> JDec.ONE.negate))
          case Kind.Strict => rows += Row(form, true, Map(i -> JDec.ONE))
          case Kind.NonStrict => rows += Row(form, false, Map(i -> JDec.ONE))
      case _ => ()
    else ()
    facts.foreach(f => add(Leaf.Fact(f), f))
    theorems.foreach(t => add(Leaf.Given(t), t.concl))
    eliminate(rows.toVector, sort == Sort.Int, leaves, limit).map(Plan(leaves.toVector, _, sort))

  /** NONLINEAR, by products (as `nlinarith`): the premises, every product of two of them (`MulNonneg`) and the square
   * of every atom (`Square`), a monomial one more variable to linear elimination — sound, not complete: what follows
   * from products of degree two */
  def refuteProducts(facts: List[Formula], theorems: List[Thm], sort: Sort, most: Int = 10, limit: Int = 6000)
      : Option[Plan] =
    import Kind.*
    val base = (facts.map(f => (Leaf.Fact(f), f)) ++ theorems.map(t => (Leaf.Given(t), t.concl)))
      .flatMap((leaf, f) => Linear.comparison(f).collect { case (l, k, s) if s == sort => (leaf, l, k) })
      .take(most)
    val leaves = mutable.ArrayBuffer.empty[Leaf]
    val rows = mutable.ArrayBuffer.empty[Row]
    def add(leaf: Leaf, form: Lin, k: Kind): Unit =
      val i = leaves.length
      leaves += leaf
      k match
        case Equal =>
          rows += Row(form, false, Map(i -> JDec.ONE))
          rows += Row(form * JDec.ONE.negate, false, Map(i -> JDec.ONE.negate))
        case Strict => rows += Row(form, true, Map(i -> JDec.ONE))
        case NonStrict => rows += Row(form, false, Map(i -> JDec.ONE))
    base.foreach((leaf, l, k) => add(leaf, l, k))
    val n = base.length
    for i <- 0 until n; j <- i until n do
      val (_, f, k1) = base(i)
      val (_, g, k2) = base(j)
      val k = if k1 == Equal || k2 == Equal then Equal else if k1 == Strict && k2 == Strict then Strict else NonStrict
      add(Leaf.Prod(i, j), Linear.times(f, g, sort), k)
    val atoms = base.flatMap(_._2.coeffs.keys).flatMap(Linear.factors).distinct
    atoms.foreach(a => add(Leaf.Sq(a), Linear.times(Lin.atom(a), Lin.atom(a), sort), NonStrict))
    eliminate(rows.toVector, sort == Sort.Int, leaves, limit).map(Plan(leaves.toVector, _, sort))

  private def contradiction(r: Row): Boolean =
    r.form.isConst && { val c = r.form.const.signum; c < 0 || (r.strict && c <= 0) }

  private def eliminate(start: Vector[Row], integers: Boolean, leaves: mutable.ArrayBuffer[Leaf], limit: Int)
      : Option[Row] =
    var rows = start.map(tighten(_, integers, leaves)).distinctBy(r => (r.form, r.strict))
    while true do
      rows.find(contradiction) match
        case Some(r) => return Some(r)
        case None => ()
      val atoms = rows.iterator.flatMap(_.form.coeffs.keysIterator).distinct.toVector
      if atoms.isEmpty then return None
      def sign(r: Row, x: Term) = r.form.coeffs.get(x).map(_.signum).getOrElse(0)
      val x = atoms.minBy(a => rows.count(sign(_, a) > 0).toLong * rows.count(sign(_, a) < 0))
      val (pos, rest) = rows.partition(sign(_, x) > 0)
      val (neg, keep) = rest.partition(sign(_, x) < 0)
      val made = for p <- pos; n <- neg yield
        val a = p.form.coeffs(x)
        val b = n.form.coeffs(x).negate
        tighten(Row(p.form * b + n.form * a, p.strict || n.strict, combine(p.prov, b, n.prov, a)), integers, leaves)
      rows = (keep ++ made).distinctBy(r => (r.form, r.strict))
      if rows.length > limit then return None
    None

  private def combine(p: Map[Int, JDec], b: JDec, n: Map[Int, JDec], a: JDec): Map[Int, JDec] =
    n.foldLeft(p.view.mapValues(_.multiply(b)).toMap) { case (m, (i, c)) =>
      val v = m.getOrElse(i, JDec.ZERO).add(c.multiply(a))
      if v.signum == 0 then m - i else m.updated(i, v)
    }

  /** over `Int`, a row whose coefficients share a factor the constant does not: the leaf of its tightening */
  private def tighten(r: Row, integers: Boolean, leaves: mutable.ArrayBuffer[Leaf]): Row =
    if !integers || r.strict || r.form.isConst || !Linear.integral(r.form) then r
    else
      val g = Linear.gcd(r.form)
      if g.compareTo(BigInteger.ONE) <= 0 || r.form.const.toBigIntegerExact.mod(g).signum == 0 then r
      else
        val gd = JDec(g)
        val i = leaves.length
        leaves += Leaf.Tight(r.prov)
        Row(Lin(r.form.coeffs.view.mapValues(_.divide(gd)).toMap, r.form.const.divide(gd, 0, java.math.RoundingMode.FLOOR)),
          false, Map(i -> JDec.ONE))

  /** the refutation as steps: `False`, from the plan's leaves */
  def emit[R[_]: Has[Infer]](plan: Plan): Thm ! R =
    val memo = mutable.Map.empty[Int, Thm]
    def leaf(i: Int): Thm ! R = memo.get(i) match
      case Some(t) => pure(t)
      case None =>
        val p: Thm ! R = plan.leaves(i) match
          case Leaf.Fact(f) => Infer.assume[R](f)
          case Leaf.Given(t) => pure(t)
          case Leaf.Tight(prov) => sum(prov).flatMap(c => Infer.step[R](Rule.Tighten(c)))
          case Leaf.Prod(a, b) => leaf(a).flatMap(x => leaf(b).flatMap(y => Infer.step[R](Rule.MulNonneg(x, y))))
          case Leaf.Sq(t) => Infer.step[R](Rule.Square(t))
        p.map { t => memo(i) = t; t }
    def sum(prov: Map[Int, JDec]): Thm ! R =
      prov.toList.sortBy(_._1).foldLeft(pure[List[(Thm, BigDecimal)], R](Nil)) { case (acc, (i, c)) =>
        acc.flatMap(l => leaf(i).map(t => l :+ (t -> BigDecimal(c))))
      }.flatMap(ps => Infer.step[R](Rule.LinComb(ps)))
    for
      combined <- sum(plan.row.prov)
      k = combined.concl match
        case Le(_, k) => Not(Le(zeroOf(plan.sort), k))
        case Lt(_, k) => Not(Lt(zeroOf(plan.sort), k))
        case other => other
      no <- Infer.compute[R](k)
      f <- Infer.step[R](Rule.NotE(no, combined))
    yield f

  private def zeroOf(s: Sort): Term = if s == Sort.Int then Term.I(0) else Term.D(BigDecimal(0))

  /** the comparison's sort, if it is one */
  def sortOf(goal: Formula): Option[Sort] = goal match
    case Not(g) => Linear.comparison(g).map(_._3)
    case g => Linear.comparison(g).map(_._3)

  /** `goal`, a comparison over `Int` or `Dec` (or a negated one), proved from `facts` (assumed: the result's
   * hypotheses) and `theorems` theorems — the steps, or `None` if no certificate is found */
  def prove[R[_]: Has[Infer]](goal: Formula, facts: List[Formula], theorems: List[Thm] = Nil): Option[Thm ! R] =
    goal match
      case _: Eq | _: Le | _: Lt if Linear.comparison(goal).exists((d, _, _) => d.isConst) && normHolds(goal) =>
        Some(Infer.step[R](Rule.Norm(goal)))
      case Eq(a, b) =>
        for
          le <- prove[R](Le(a, b), facts, theorems)
          ge <- prove[R](Le(b, a), facts, theorems)
        yield le.flatMap(x => ge.flatMap(y => Infer.step[R](Rule.Antisym(x, y))))
      case Not(g) if Linear.comparison(g).isDefined =>
        // refute g itself: assume it, reach False, discharge
        for s <- sortOf(g); f <- falsum[R](g, facts, theorems, s)
        yield f.flatMap(f => Infer.step[R](Rule.NotI(g, f)))
      case g if Linear.comparison(g).isDefined =>
        for s <- sortOf(g); f <- falsum[R](Not(g), facts, theorems, s)
        yield f.flatMap(f => Infer.step[R](Rule.NotI(Not(g), f))).flatMap(n => Infer.step[R](Rule.Classic(n)))
      case _ => None

  private def normHolds(goal: Formula): Boolean = Linear.comparison(goal).exists { (d, k, _) =>
    val c = d.const.signum
    k match
      case Kind.Equal => c == 0
      case Kind.NonStrict => c >= 0
      case Kind.Strict => c > 0
  }

  /** `goal` from `facts` and `theorems` under `k`: the theorem, `Right(None)` if no certificate is found */
  def decide(k: Kernel, goal: Formula, facts: List[Formula], theorems: List[Thm] = Nil): Either[String, Option[Thm]] =
    prove[Infer](goal, facts, theorems) match
      case None => Right(None)
      case Some(p) => run(Infer.by(k)(p)).map(Some(_))
