package okay.proof

import scala.util.hashing.MurmurHash3

/** a node's hash from its parts' (each cached): cheap, done once as the node is built */
private[proof] inline def mix(tag: Int, a: Int): Int =
  MurmurHash3.finalizeHash(MurmurHash3.mix(MurmurHash3.mix(0x9e3779b9, tag), a), 1)
private[proof] inline def mix(tag: Int, a: Int, b: Int): Int =
  MurmurHash3.finalizeHash(MurmurHash3.mix(MurmurHash3.mix(MurmurHash3.mix(0x9e3779b9, tag), a), b), 2)
private[proof] inline def mix(tag: Int, a: Int, b: Int, c: Int): Int =
  MurmurHash3.finalizeHash(MurmurHash3.mix(MurmurHash3.mix(MurmurHash3.mix(MurmurHash3.mix(0x9e3779b9, tag), a), b), c), 3)

private[proof] def listHash(xs: List[Any]): Int =
  var h = 17
  var l = xs
  while l.nonEmpty do { h = MurmurHash3.mix(h, l.head.hashCode); l = l.tail }
  MurmurHash3.finalizeHash(h, 0)

/** the union of two sets of free variables, the common cases — one or both empty — with nothing made */
private[proof] inline def union[A](a: Set[A], b: Set[A]): Set[A] =
  if a.isEmpty then b else if b.isEmpty then a else a ++ b

/**
 * THE LOGIC: many-sorted first-order logic with equality. Sorts: exact integers, exact decimals, strings, and sorts of
 * one's own (`Sort.Named("Account")`). Terms: variables, literals, applications of functions — the kernel's own
 * (`Fn.add`, `Fn.round` …: interpreted, computed exactly) or one's own (`limit(role)`: uninterpreted, known only by
 * axioms and facts). Formulas: `True`, `False`, `=`, `<`, `≤`, predicates of one's own, the connectives and the
 * quantifiers. Every node caches its hash (built bottom-up), so sets of hypotheses and comparisons stay cheap.
 */
enum Sort:
  case Int, Dec, Str
  case Named(name: String)

/** a function: interpreted when it is one of `Fn`'s own, by its name and sorts */
final case class Fn(name: String, args: List[Sort], result: Sort):
  override val hashCode: Int = mix(1, name.hashCode, listHash(args), result.hashCode)

/** a predicate of one's own: known only by axioms and facts */
final case class Pred(name: String, args: List[Sort]):
  override val hashCode: Int = mix(2, name.hashCode, listHash(args))

sealed trait Term:
  /** the term's KEY: a text naming it, the same in every language that reads certificates (okay-lean's checker
   * builds it alike) — what orders the atoms of a polynomial, so that both build its term the same way */
  lazy val key: String = Logic.key(this)

  /** the free variables, computed once when asked */
  lazy val free: Set[Term.V] = this match
    case v: Term.V => Set(v)
    case Term.Ap(_, as) => as.foldLeft(Set.empty[Term.V])((acc, t) => union(acc, t.free))
    case _ => Set.empty

object Term:
  final case class V(name: String, sort: Sort) extends Term:
    override val hashCode: Int = mix(3, name.hashCode, sort.hashCode)
    override def toString = name
  final case class I(value: BigInt) extends Term:
    override val hashCode: Int = mix(4, value.hashCode)
    override def toString = value.toString
  final case class D(value: BigDecimal) extends Term:
    override val hashCode: Int = mix(5, value.hashCode)
    override def toString = Logic.plain(value.bigDecimal)
  final case class S(value: String) extends Term:
    override val hashCode: Int = mix(6, value.hashCode)
    override def toString = "\"" + value + "\""
  final case class Ap(fn: Fn, args: List[Term]) extends Term:
    override val hashCode: Int = mix(7, fn.hashCode, listHash(args))
    override def toString = if args.isEmpty then fn.name else s"${fn.name}(${args.mkString(", ")})"

sealed trait Formula:
  lazy val free: Set[Term.V] = this match
    case Formula.Eq(a, b) => union(a.free, b.free)
    case Formula.Lt(a, b) => union(a.free, b.free)
    case Formula.Le(a, b) => union(a.free, b.free)
    case Formula.P(_, as) => as.foldLeft(Set.empty[Term.V])((acc, t) => union(acc, t.free))
    case Formula.Not(f) => f.free
    case Formula.And(a, b) => union(a.free, b.free)
    case Formula.Or(a, b) => union(a.free, b.free)
    case Formula.Imp(a, b) => union(a.free, b.free)
    case Formula.All(x, f) => if f.free.contains(x) then f.free - x else f.free
    case Formula.Ex(x, f) => if f.free.contains(x) then f.free - x else f.free
    case _ => Set.empty

  def &&(that: Formula): Formula = Formula.And(this, that)
  def ||(that: Formula): Formula = Formula.Or(this, that)
  /** `a && b implies c` is `(a ∧ b) → c`: a word, so it binds the loosest (a symbol such as `==>` would bind tighter
   * than `&&`, Scala's precedence going by the first character) */
  infix def implies(that: Formula): Formula = Formula.Imp(this, that)
  def unary_! : Formula = Formula.Not(this)

object Formula:
  case object True extends Formula
  case object False extends Formula
  final case class Eq(a: Term, b: Term) extends Formula:
    override val hashCode: Int = mix(8, a.hashCode, b.hashCode)
    override def toString = s"$a = $b"
  final case class Lt(a: Term, b: Term) extends Formula:
    override val hashCode: Int = mix(9, a.hashCode, b.hashCode)
    override def toString = s"$a < $b"
  final case class Le(a: Term, b: Term) extends Formula:
    override val hashCode: Int = mix(10, a.hashCode, b.hashCode)
    override def toString = s"$a ≤ $b"
  final case class P(pred: Pred, args: List[Term]) extends Formula:
    override val hashCode: Int = mix(11, pred.hashCode, listHash(args))
    override def toString = s"${pred.name}(${args.mkString(", ")})"
  final case class Not(f: Formula) extends Formula:
    override val hashCode: Int = mix(12, f.hashCode)
    override def toString = s"¬$f"
  final case class And(a: Formula, b: Formula) extends Formula:
    override val hashCode: Int = mix(13, a.hashCode, b.hashCode)
    override def toString = s"($a ∧ $b)"
  final case class Or(a: Formula, b: Formula) extends Formula:
    override val hashCode: Int = mix(14, a.hashCode, b.hashCode)
    override def toString = s"($a ∨ $b)"
  final case class Imp(a: Formula, b: Formula) extends Formula:
    override val hashCode: Int = mix(15, a.hashCode, b.hashCode)
    override def toString = s"($a → $b)"
  final case class All(x: Term.V, f: Formula) extends Formula:
    override val hashCode: Int = mix(16, x.hashCode, f.hashCode)
    override def toString = s"∀$x. $f"
  final case class Ex(x: Term.V, f: Formula) extends Formula:
    override val hashCode: Int = mix(17, x.hashCode, f.hashCode)
    override def toString = s"∃$x. $f"

  /** `∀x̄. f`, the variables bound left to right */
  def all(xs: Term.V*)(f: Formula): Formula = xs.foldRight(f)(All(_, _))

/** sorts, substitution: what the kernel checks and computes with — no trust beyond being correct */
object Logic:
  import Formula.*
  import Term.*

  private def cps(s: String): Int = s.codePointCount(0, s.length)
  private def named(s: String): String = s"${cps(s)}:$s"

  def sortKey(s: Sort): String = s match
    case Sort.Int => "I"
    case Sort.Dec => "D"
    case Sort.Str => "S"
    case Sort.Named(n) => "N" + named(n)

  /** a decimal's text: its value, no trailing zero, no exponent */
  def plain(d: java.math.BigDecimal): String =
    if d.signum == 0 then "0" else d.stripTrailingZeros.toPlainString

  /** a term's key, by its structure: names prefixed by their length, so no two terms share one */
  def key(t: Term): String = t match
    case V(n, s) => "v" + named(n) + sortKey(s)
    case I(v) => "i" + v.toString + ";"
    case D(v) => "d" + plain(v.bigDecimal) + ";"
    case S(v) => "s" + named(v)
    case Ap(fn, as) =>
      "a" + named(fn.name) + fn.args.length + "(" + fn.args.map(sortKey).mkString + ")" + sortKey(fn.result) + "[" +
        as.map(_.key).mkString + "]"

  /** texts compared by code points, as Lean compares its strings */
  val byCodePoints: Ordering[String] = (a, b) =>
    // walked by `codePointAt`, no array made (and no `codePoints` stream, which Scala.js has not)
    var i, j = 0
    var order = 0
    while order == 0 && i < a.length && j < b.length do
      val x = a.codePointAt(i)
      val y = b.codePointAt(j)
      order = Integer.compare(x, y)
      i += Character.charCount(x)
      j += Character.charCount(y)
    if order != 0 then order else Integer.compare(a.codePointCount(i, a.length), b.codePointCount(j, b.length))

  /** terms in the order of their keys */
  val termOrder: Ordering[Term] = Ordering.by[Term, String](_.key)(using byCodePoints)

  /** a term's sort, if it is well-sorted */
  def sortOf(t: Term): Option[Sort] = t match
    case V(_, s) => Some(s)
    case I(_) => Some(Sort.Int)
    case D(_) => Some(Sort.Dec)
    case S(_) => Some(Sort.Str)
    case Ap(fn, as) => if fits(as, fn.args) then Some(fn.result) else None

  /** each term of `as` of the sort at its place in `ss`, as many */
  private def fits(as: List[Term], ss: List[Sort]): Boolean =
    var a = as
    var s = ss
    while a.nonEmpty && s.nonEmpty do
      if !sortOf(a.head).contains(s.head) then return false
      a = a.tail
      s = s.tail
    a.isEmpty && s.isEmpty

  /** a formula is well-sorted: equal sorts on both sides of `=`, numbers on both sides of `<` and `≤`, arguments as
   * their symbols say */
  def wellSorted(f: Formula): Boolean = f match
    case True | False => true
    case Eq(a, b) => sortOf(a).isDefined && sortOf(a) == sortOf(b)
    case Lt(a, b) => numeric(a, b)
    case Le(a, b) => numeric(a, b)
    case P(p, as) => fits(as, p.args)
    case Not(g) => wellSorted(g)
    case And(a, b) => wellSorted(a) && wellSorted(b)
    case Or(a, b) => wellSorted(a) && wellSorted(b)
    case Imp(a, b) => wellSorted(a) && wellSorted(b)
    case All(_, g) => wellSorted(g)
    case Ex(_, g) => wellSorted(g)

  private def numeric(a: Term, b: Term): Boolean =
    val s = sortOf(a)
    s == sortOf(b) && (s.contains(Sort.Int) || s.contains(Sort.Dec))

  /** `t` with `x` replaced by `by` */
  def subst(t: Term, x: V, by: Term): Term = t match
    case v: V => if v == x then by else v
    case Ap(fn, as) => if t.free.contains(x) then Ap(fn, as.map(subst(_, x, by))) else t
    case _ => t

  /** `f` with the free `x` replaced by `by`, no variable of `by` captured: a binder in the way renamed */
  def subst(f: Formula, x: V, by: Term): Formula =
    if !f.free.contains(x) then f
    else f match
      case Eq(a, b) => Eq(subst(a, x, by), subst(b, x, by))
      case Lt(a, b) => Lt(subst(a, x, by), subst(b, x, by))
      case Le(a, b) => Le(subst(a, x, by), subst(b, x, by))
      case P(p, as) => P(p, as.map(subst(_, x, by)))
      case Not(g) => Not(subst(g, x, by))
      case And(a, b) => And(subst(a, x, by), subst(b, x, by))
      case Or(a, b) => Or(subst(a, x, by), subst(b, x, by))
      case Imp(a, b) => Imp(subst(a, x, by), subst(b, x, by))
      case All(y, g) => binder(y, g, x, by)(All(_, _))
      case Ex(y, g) => binder(y, g, x, by)(Ex(_, _))
      case other => other

  private def binder(y: V, g: Formula, x: V, by: Term)(make: (V, Formula) => Formula): Formula =
    if y == x then make(y, g)
    else if by.free.contains(y) then
      val y2 = fresh(y, by.free ++ g.free + x)
      make(y2, subst(subst(g, y, y2), x, by))
    else make(y, subst(g, x, by))

  /** a variable like `y`, none of `avoid` */
  def fresh(y: V, avoid: Set[V]): V =
    Iterator.from(1).map(i => V(s"${y.name}$i", y.sort)).find(v => !avoid.exists(_.name == v.name)).get

  /** two formulas equal up to the names of bound variables */
  def alphaEq(a: Formula, b: Formula): Boolean = (a eq b) || (a.hashCode == b.hashCode && a == b) || ((a, b) match
    case (All(x, f), All(y, g)) => x.sort == y.sort && alphaBody(x, f, y, g)
    case (Ex(x, f), Ex(y, g)) => x.sort == y.sort && alphaBody(x, f, y, g)
    case (Not(f), Not(g)) => alphaEq(f, g)
    case (And(a1, b1), And(a2, b2)) => alphaEq(a1, a2) && alphaEq(b1, b2)
    case (Or(a1, b1), Or(a2, b2)) => alphaEq(a1, a2) && alphaEq(b1, b2)
    case (Imp(a1, b1), Imp(a2, b2)) => alphaEq(a1, a2) && alphaEq(b1, b2)
    case _ => false)

  private def alphaBody(x: V, f: Formula, y: V, g: Formula): Boolean =
    if x == y then alphaEq(f, g)
    else
      val z = fresh(x, f.free ++ g.free + x + y)
      alphaEq(subst(f, x, z), subst(g, y, z))
