package okay.proof

import Formula.*
import Term.*

/**
 * A SYNTAX for writing formulas as one reads them — `owns(u, a) && spent(u) + amt <= 1000.00 implies
 * mayTransfer(u, a, amt)` — that builds the same `Term`s and `Formula`s as the constructors do. Not trusted: it only
 * builds data, which the kernel checks as it would any other.
 *
 *  - symbols are applied like functions: `spent(u)`, `owns(u, a)`; a literal argument becomes a term of the sort
 *    its place asks for (`mayTransfer(ann, acc1, 700)`: `700` a `Dec` there);
 *  - `+ - *` and unary `-` pick the kernel's function by the operands' sort (`+` over `Int`, `d+` over `Dec`, `++`
 *    over `Str`); `< <= > >=`, `===` and `=/=` compare; a literal on the right takes the left side's sort;
 *  - precedence is Scala's, by the first character: `* ` before `+ -`, before `< >`, before `=`, before `&&`, before
 *    `||`, and the word `implies` last — so the formula above reads as it is meant.
 *
 * A term of the wrong sort, or a literal that cannot be one of the sort asked for (`1.5` as an `Int`), is an
 * `IllegalArgumentException` at once, not a formula the kernel refuses later. A `Double` literal is read by its
 * shortest decimal text (`700.01` is exactly 700.01); for a decimal computed elsewhere, pass a `BigDecimal`.
 */
object syntax:
  /** what a symbol or an operator takes: a term, or a literal made a term of the sort asked for */
  type Arg = Term | Int | Long | BigInt | BigDecimal | Double | String

  def sort(name: String): Sort = Sort.Named(name)
  def v(name: String, sort: Sort): V = V(name, sort)
  def const(name: String, sort: Sort): Term = Ap(Fn(name, Nil, sort), Nil)
  /** a function of one's own: `fn("spent", User)(Sort.Dec)` */
  def fn(name: String, args: Sort*)(result: Sort): Fn = Fn(name, args.toList, result)
  def pred(name: String, args: Sort*): Pred = Pred(name, args.toList)

  def int(n: BigInt): Term = I(n)
  /** an exact decimal from its text: `dec("1000.00")` */
  def dec(s: String): Term = D(BigDecimal(s))
  def str(s: String): Term = S(s)

  /** `∀x̄. f` and `∃x̄. f`, the variables bound left to right */
  def forall(xs: V*)(f: Formula): Formula = Formula.all(xs*)(f)
  def exists(xs: V*)(f: Formula): Formula = xs.foldRight(f)(Ex(_, _))

  private def fail(why: String): Nothing = throw IllegalArgumentException(why)

  private def sortOf(t: Term): Sort = Logic.sortOf(t).getOrElse(fail(s"ill-sorted term: $t"))

  /** `x` as a term of `s` */
  def term(x: Arg, s: Sort): Term = x match
    case t: Term => if sortOf(t) == s then t else fail(s"$t is of sort ${sortOf(t)}, not $s")
    case n: Int => number(BigDecimal(n), s, x)
    case n: Long => number(BigDecimal(n), s, x)
    case n: BigInt => number(BigDecimal(n), s, x)
    case d: BigDecimal => number(d, s, x)
    case d: Double => number(BigDecimal(d), s, x)
    case t: String => if s == Sort.Str then S(t) else fail(s"\"$t\" is a string, not $s")

  private def number(d: BigDecimal, s: Sort, x: Arg): Term = s match
    case Sort.Dec => D(d)
    case Sort.Int if d.isWhole => I(d.toBigInt)
    case _ => fail(s"$x is not of sort $s")

  /** `x` as a term of its own sort: a whole number an `Int`, a fraction a `Dec`, text a `Str` */
  def term(x: Arg): Term = x match
    case t: Term => t
    case n: Int => I(n)
    case n: Long => I(n)
    case n: BigInt => I(n)
    case d: BigDecimal => D(d)
    case d: Double => D(BigDecimal(d))
    case t: String => S(t)

  private def args(name: String, sorts: List[Sort], xs: Seq[Arg]): List[Term] =
    if xs.length != sorts.length then fail(s"$name takes ${sorts.length} arguments, not ${xs.length}")
    xs.lazyZip(sorts).map(term).toList

  extension (f: Fn) def apply(xs: Arg*): Term = Ap(f, args(f.name, f.args, xs))
  extension (p: Pred) def apply(xs: Arg*): Formula = P(p, args(p.name, p.args, xs))

  private def op(a: Term, b: Arg, sym: String)(int: Fn, dec: Fn, str: Fn | Null = null): Term =
    sortOf(a) match
      case Sort.Int => Ap(int, List(a, term(b, Sort.Int)))
      case Sort.Dec => Ap(dec, List(a, term(b, Sort.Dec)))
      case Sort.Str if str != null => Ap(str, List(a, term(b, Sort.Str)))
      case s => fail(s"no $sym over $s")

  extension (a: Term)
    def +(b: Arg): Term = op(a, b, "+")(Fns.add, Fns.dadd, Fns.concat)
    def -(b: Arg): Term = op(a, b, "-")(Fns.sub, Fns.dsub)
    def *(b: Arg): Term = op(a, b, "*")(Fns.mul, Fns.dmul)
    def unary_- : Term = sortOf(a) match
      case Sort.Int => Ap(Fns.neg, List(a))
      case Sort.Dec => Ap(Fns.dsub, List(D(0), a))
      case s => fail(s"no - over $s")
    def <(b: Arg): Formula = Lt(a, term(b, sortOf(a)))
    def <=(b: Arg): Formula = Le(a, term(b, sortOf(a)))
    def >(b: Arg): Formula = Lt(term(b, sortOf(a)), a)
    def >=(b: Arg): Formula = Le(term(b, sortOf(a)), a)
    def ===(b: Arg): Formula = Eq(a, term(b, sortOf(a)))
    def =/=(b: Arg): Formula = Not(Eq(a, term(b, sortOf(a))))
