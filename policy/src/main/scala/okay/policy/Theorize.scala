package okay.policy

import okay.proof.{Fn, Fns, Formula, Kernel, Pred, Term, Theory}
import okay.proof.Formula as F

/**
 * A POLICY AS A THEORY of okay-proof: its sorts, its facts and states function symbols or predicates, each call's
 * verdicts predicates over the caller and its arguments, each rule an axiom —
 * `∀ caller, args. condition ⇒ allow:tool(caller, args)`. The kernel of that theory is the only maker of decisions.
 */
final class Theorize(val checked: Checked):
  def sort(s: Sort): okay.proof.Sort = s match
    case Sort.Int => okay.proof.Sort.Int
    case Sort.Dec => okay.proof.Sort.Dec
    case Sort.Text => okay.proof.Sort.Str
    case Sort.Entity(n) => okay.proof.Sort.Named(n)

  def term(v: Value): Term = v match
    case Value.I(x) => Term.I(x)
    case Value.D(x) => Term.D(x)
    case Value.T(x) => Term.S(x)
    case Value.E(s, n) => Term.Ap(Fn(n, Nil, okay.proof.Sort.Named(s)), Nil)

  private val callerSort = Sort.Entity(Types.callerType)

  val factFns: Map[String, Fn] = checked.facts.values.collect {
    case FactSig(n, ps, Some(r), _) => n -> Fn(n, ps.map(sort), sort(r))
  }.toMap ++ checked.states.values.map(s => s.name -> Fn(s.name, s.params.map(sort), sort(s.sort)))

  val preds: Map[String, Pred] = checked.facts.values.collect {
    case FactSig(n, ps, None, _) => n -> Pred(n, ps.map(sort))
  }.toMap

  /** the verdict's predicate of a tool: over the caller and the tool's arguments, in their order */
  def verdict(v: Verdict, tool: String): Pred =
    Pred(s"${v.word}:$tool", (callerSort :: checked.calls(tool).params.map(_._2)).map(sort))

  /** a rule's variables for a tool: the caller, then the tool's arguments */
  def vars(tool: String): List[Term.V] =
    Term.V("caller", sort(callerSort)) :: checked.calls(tool).params.map((n, s) => Term.V(n, sort(s)))

  def axiomName(r: TRule, tool: String): String = s"rule ${r.index + 1} (line ${r.source.pos.line}) on $tool"

  /** the term of an expression, its variables free */
  def term(e: TExpr): Term = e match
    case TExpr.Lit(v) => term(v)
    case TExpr.Var("tool", _) => Term.V("tool", okay.proof.Sort.Str)
    case TExpr.Var(n, s) => Term.V(n, sort(s))
    case TExpr.Fact(n, as, _) => Term.Ap(factFns(n), as.map(term))
    case TExpr.State(n, as, _) => Term.Ap(factFns(n), as.map(term))
    case TExpr.Add(a, b, s) => Term.Ap(if s == Sort.Int then Fns.add else Fns.dadd, List(term(a), term(b)))
    case TExpr.Sub(a, b, s) => Term.Ap(if s == Sort.Int then Fns.sub else Fns.dsub, List(term(a), term(b)))
    case TExpr.Mul(a, by, s) => Term.Ap(if s == Sort.Int then Fns.mul else Fns.dmul, List(term(a), term(by)))
    case TExpr.ToDec(a) => Term.Ap(Fns.dec, List(term(a)))

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
    case TCond.Holds(n, as) => F.P(preds(n), as.map(term))
    case TCond.And(a, b) => F.And(formula(a), formula(b))
    case TCond.Or(a, b) => F.Or(formula(a), formula(b))
    case TCond.Not(a) => F.Not(formula(a))

  /** `tool` is the text of the tool's name in a rule about it */
  private def named(tool: String)(f: Formula): Formula = okay.proof.Logic.subst(f, Term.V("tool", okay.proof.Sort.Str),
    Term.S(tool))

  /** a rule's axiom for one of its tools; none for an `allow` with no condition (it only counts) */
  def axiom(r: TRule, tool: String): Option[(String, Formula)] =
    val head = F.P(verdict(r.verdict, tool), vars(tool))
    val body = r.when.map(c => named(tool)(formula(c)))
    if r.when.isEmpty && r.verdict == Verdict.Allow then None
    else Some(axiomName(r, tool) -> Formula.all(vars(tool)*)(body.fold(head)(_ implies head)))

  val theory: Theory = Theory(checked.policy.name, (for
    r <- checked.rules
    t <- r.tools
    a <- axiom(r, t)
  yield a)*)

  /** the kernel of the policy: the only maker of its decisions */
  val kernel: Kernel = Kernel(theory)
