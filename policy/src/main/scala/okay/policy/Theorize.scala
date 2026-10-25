package okay.policy

import okay.proof.{Fn, Fns, Formula, Kernel, Pred, Term, Theory}
import okay.proof.Formula as F

/**
 * A POLICY AS A THEORY of okay-proof: its sorts, its facts and states function symbols or predicates, the call an
 * entity whose arguments are facts about it, each tool's verdicts predicates over the caller and the call, each rule
 * an axiom — `∀ caller, call. condition ⇒ allow:tool(caller, call)`. The kernel of that theory is the only maker of
 * decisions.
 */
final class Theorize(val checked: Checked):
  def sort(s: Sort): okay.proof.Sort = s match
    case Sort.Int => okay.proof.Sort.Int
    case Sort.Dec => okay.proof.Sort.Dec
    case Sort.Text => okay.proof.Sort.Str
    case Sort.Entity(n) => okay.proof.Sort.Named(n)
    case Sort.Rec(n) => okay.proof.Sort.Named(n)
    case Sort.ListOf(e) => throw IllegalArgumentException(s"a list is no sort of the logic: List[$e]")

  def term(v: Value): Term = v match
    case Value.I(x) => Term.I(x)
    case Value.D(x) => Term.D(x)
    case Value.T(x) => Term.S(x)
    case Value.E(s, n) => Term.Ap(Fn(n, Nil, okay.proof.Sort.Named(s)), Nil)

  /** a function fact, a state, an argument or a field of the call: a symbol applied to one argument or more, not
   * the kernel's own */
  def isFact(fn: Fn): Boolean = fn.args.nonEmpty && !Fns.all.contains(fn)

  private val callerSort = Sort.Entity(Types.callerType)
  private val callSort = Sort.Entity(Types.callType)

  /** the verdict's predicate of a tool: over the caller and the call */
  def verdict(v: Verdict, tool: String): Pred = Pred(s"${v.word}:$tool", List(sort(callerSort), sort(callSort)))

  /** a rule's variables: the caller, the call */
  def vars(tool: String): List[Term.V] = List(Term.V("caller", sort(callerSort)), Term.V("call", sort(callSort)))

  def axiomName(r: TRule, tool: String): String = s"rule ${r.index + 1} (line ${r.source.pos.line}) on $tool"

  /** the term of an expression, its variables free */
  def term(e: TExpr): Term = e match
    case TExpr.Lit(v) => term(v)
    case TExpr.Var(n, s) => Term.V(n, sort(s))
    case TExpr.Fact(n, as, s) => Term.Ap(Fn(n, as.map(a => sort(a.sort)), sort(s)), as.map(term))
    case TExpr.State(n, as, s) => Term.Ap(Fn(n, as.map(a => sort(a.sort)), sort(s)), as.map(term))
    case TExpr.Add(a, b, s) => Term.Ap(if s == Sort.Int then Fns.add else Fns.dadd, List(term(a), term(b)))
    case TExpr.Sub(a, b, s) => Term.Ap(if s == Sort.Int then Fns.sub else Fns.dsub, List(term(a), term(b)))
    case TExpr.Mul(a, by, s) => Term.Ap(if s == Sort.Int then Fns.mul else Fns.dmul, List(term(a), term(by)))
    case TExpr.ToDec(a) => Term.Ap(Fns.dec, List(term(a)))

  /** a list's membership: `items(call, x)` */
  def member(l: TList, x: Term): Formula =
    F.P(Pred(l.name, List(sort(l.base.sort), sort(l.elem))), List(term(l.base), x))

  def formula(c: TCond): Formula = c match
    case TCond.Compare(a, cmp, b) =>
      val (x, y) = (term(a), term(b))
      cmp match
        case Cmp.Eq => F.Eq(x, y)
        case Cmp.Ne => F.Not(F.Eq(x, y))
        case Cmp.Lt => F.Lt(x, y)
        case Cmp.Le => F.Le(x, y)
        case Cmp.Gt => F.Lt(y, x)
        case Cmp.Ge => F.Le(y, x)
    case TCond.In(a, os) =>
      val x = term(a)
      os.map(o => F.Eq(x, term(o)): Formula).reduceRight(F.Or(_, _))
    case TCond.Holds(n, as) => F.P(Pred(n, as.map(a => sort(a.sort))), as.map(term))
    case TCond.Text(a, op, b) =>
      val (x, y) = (term(a), term(b))
      op match
        case TextOp.Starts => F.Eq(Term.Ap(Fns.take, List(x, Term.Ap(Fns.length, List(y)))), y)
        case TextOp.Ends => F.Eq(Term.Ap(Fns.takeRight, List(x, Term.Ap(Fns.length, List(y)))), y)
        case TextOp.Contains => F.Le(Term.I(0), Term.Ap(Fns.indexOf, List(x, y)))
    case TCond.And(a, b) => F.And(formula(a), formula(b))
    case TCond.Or(a, b) => F.Or(formula(a), formula(b))
    case TCond.Not(a) => F.Not(formula(a))
    case TCond.Every(x, l, b) =>
      val v = Term.V(x, sort(l.elem))
      F.All(v, F.Imp(member(l, v), formula(b)))
    case TCond.Exists(x, l, b) =>
      val v = Term.V(x, sort(l.elem))
      F.Ex(v, F.And(member(l, v), formula(b)))

  /** `tool` is the text of the tool's name in a rule about it */
  private def named(tool: String)(f: Formula): Formula = okay.proof.Logic.subst(f, Term.V("tool", okay.proof.Sort.Str),
    Term.S(tool))

  /** a rule's axiom for one of its tools */
  def axiom(r: TRule, tool: String): (String, Formula) =
    val head = F.P(verdict(r.verdict, tool), vars(tool))
    val body = r.when.map(c => named(tool)(formula(c)))
    axiomName(r, tool) -> Formula.all(vars(tool)*)(body.fold(head)(_ implies head))

  val theory: Theory = Theory(checked.policy.name, (for
    r <- checked.rules
    t <- r.tools
  yield axiom(r, t))*)

  /** the kernel of the policy: the only maker of its decisions */
  val kernel: Kernel = Kernel(theory)
