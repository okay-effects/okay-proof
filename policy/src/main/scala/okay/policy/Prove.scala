package okay.policy

import okay.proof.{Arithmetic, Formula, Infer, Logic, Rule, Term, Thm}
import okay.proof.Formula as F
import okay.scala3.*

/**
 * A DECISION'S PROOF, built from the evaluation — no search. For the rule that applies: its axiom, `∀` out with the
 * call's values, its condition proved part by part, `ImpE`. A relation fact is assumed (a hypothesis: the guard knows
 * it); an atom with facts in it is computed with their values in their places and turned back into its facts by
 * `Subst` with each fact's equation, assumed. Every step goes through `Infer`, so the kernel checks it — a wrong turn
 * here makes the proof fail, never a wrong theorem.
 */
final class Prove(t: Theorize):
  /** an expression with the call's values in place of its variables */
  private def bind(e: TExpr, env: Map[String, Value]): TExpr = e match
    case v @ TExpr.Var(n, _) => env.get(n).fold(v)(TExpr.Lit(_))
    case TExpr.Fact(n, as, s) => TExpr.Fact(n, as.map(bind(_, env)), s)
    case TExpr.State(n, as, s) => TExpr.State(n, as.map(bind(_, env)), s)
    case TExpr.Add(a, b, s) => TExpr.Add(bind(a, env), bind(b, env), s)
    case TExpr.Sub(a, b, s) => TExpr.Sub(bind(a, env), bind(b, env), s)
    case TExpr.Mul(a, by, s) => TExpr.Mul(bind(a, env), by, s)
    case TExpr.ToDec(a) => TExpr.ToDec(bind(a, env))
    case lit => lit

  def bind(c: TCond, env: Map[String, Value]): TCond = c match
    case TCond.Compare(a, cmp, b) => TCond.Compare(bind(a, env), cmp, bind(b, env))
    case TCond.In(a, os) => TCond.In(bind(a, env), os.map(bind(_, env)))
    case TCond.Holds(n, as) => TCond.Holds(n, as.map(bind(_, env)))
    case TCond.Text(a, op, b) => TCond.Text(bind(a, env), op, bind(b, env))
    case TCond.And(a, b) => TCond.And(bind(a, env), bind(b, env))
    case TCond.Or(a, b) => TCond.Or(bind(a, env), bind(b, env))
    case TCond.Not(a) => TCond.Not(bind(a, env))
    case TCond.Every(x, l, b) => TCond.Every(x, l.copy(base = bind(l.base, env)), bind(b, env - x))
    case TCond.Exists(x, l, b) => TCond.Exists(x, l.copy(base = bind(l.base, env)), bind(b, env - x))

  /** the theorem that `rule` decides `call`: its condition holding under `known` (checked by the evaluator first) */
  def decision[R[_]: Has[Infer]](rule: TRule, call: Call, known: Known): Thm ! R =
    val env = call.env
    val (name, values, when) = t.instance(rule, call.tool, t.term(env("caller")), t.term(env("call")))
    val axiom = Infer.axiom[R](name)
    val instance = values.foldLeft(axiom)((p, v) => p.flatMap(th => Infer.allE[R](th, v)))
    when match
      case None => instance
      case Some(c) =>
        val bound = bind(c, env)
        for
          imp <- instance
          cond <- holds[R](bound, known)
          thm <- Infer.impE[R](imp, cond)
        yield thm

  /** a closed condition proved: the evaluator found it true */
  private def holds[R[_]: Has[Infer]](c: TCond, known: Known): Thm ! R = c match
    case TCond.And(a, b) =>
      for x <- holds[R](a, known); y <- holds[R](b, known); t <- Infer.andI[R](x, y) yield t
    case TCond.Or(a, b) =>
      if Eval.holds(a, Map.empty, known).contains(true) then
        holds[R](a, known).flatMap(x => Infer.step[R](Rule.OrI1(x, t.formula(b))))
      else holds[R](b, known).flatMap(y => Infer.step[R](Rule.OrI2(t.formula(a), y)))

    case TCond.Every(x, l, body) => every[R](x, l, body, known)
    case TCond.Exists(x, l, body) =>
      val es = Eval.elements(l, Map.empty, known).getOrElse(Nil)
      es.find(e => Eval.holds(bind(body, Map(x -> e)), Map.empty, known).contains(true)) match
        case None => Infer.refuse[R](s"no element of ${l.name} holds")
        case Some(e) =>
          val v = Term.V(x, t.sort(l.elem))
          for
            m <- Infer.assume[R](t.member(l, t.term(e)))
            pe <- holds[R](bind(body, Map(x -> e)), known)
            both <- Infer.andI[R](m, pe)
            ex <- Infer.step[R](Rule.ExI(v, F.And(t.member(l, v), t.formula(body)), t.term(e), both))
          yield ex
    case _ => atom[R](t.formula(c), known)

  /**
   * `∀x. list(base, x) ⇒ body`: the list given CLOSED — `∀e. list(base, e) ⇒ e = e0 ∨ … ∨ e(n-1)`, a hypothesis
   * from the call — so for an `x` in the list it is one of the elements, by cases (`OrE`); in each case the body
   * proved of that element and carried over to `x` by `Subst`; `x` then generalized (`AllI`)
   */
  private def every[R[_]: Has[Infer]](x: String, l: TList, body: TCond, known: Known): Thm ! R =
    val es = Eval.elements(l, Map.empty, known).getOrElse(Nil)
    val sortX = t.sort(l.elem)
    val v = Term.V(x, sortX)
    val p = t.formula(body)
    def oneOf(y: Term): Formula =
      if es.isEmpty then F.False else es.map(e => F.Eq(y, t.term(e)): Formula).reduceRight(F.Or(_, _))
    val e0 = Term.V("§e", sortX)
    val closure = F.All(e0, F.Imp(t.member(l, e0), oneOf(e0)))
    /** `body(x)`, from `x = e`: the body of `e` carried over */
    def carried(eq: Thm, e: Value): Thm ! R =
      val r = Term.V("§r", sortX)
      for
        refl <- Infer.refl[R](v)
        back <- Infer.subst[R](eq, r, F.Eq(r, v), refl) // e = x
        pe <- holds[R](bind(body, Map(x -> e)), known)
        px <- Infer.subst[R](back, v, p, pe)
      yield px
    /** `body(x)` from `x` one of `rest` */
    def cases(d: Thm, rest: List[Value]): Thm ! R = rest match
      case Nil => Infer.step[R](Rule.FalseE(d, p))
      case List(e) => carried(d, e)
      case e :: more =>
        val restFormula = more.map(m => F.Eq(v, t.term(m)): Formula).reduceRight(F.Or(_, _))
        for
          first <- Infer.assume[R](F.Eq(v, t.term(e))).flatMap(carried(_, e))
          others <- Infer.assume[R](restFormula).flatMap(cases(_, more))
          both <- Infer.step[R](Rule.OrE(d, first, others))
        yield both
    for
      c <- Infer.assume[R](closure)
      inst <- Infer.allE[R](c, v)
      m <- Infer.assume[R](t.member(l, v))
      d <- Infer.impE[R](inst, m)
      px <- cases(d, es)
      imp <- Infer.impI[R](t.member(l, v), px)
      all <- Infer.allI[R](v, imp)
    yield all

  /** a fact's or a state's value as a term: its arguments values already (`balance(acc1)`), read from what is known */
  private def valueOf(fn: okay.proof.Fn, args: List[Term], known: Known): Option[Term] =
    val key = FactRef(fn.name, args.map(valueOfTerm))
    known.facts.get(key) match
      case Some(Answer.Is(v)) => Some(t.term(v))
      case _ => known.states.get(key).map(t.term)

  private def valueOfTerm(x: Term): Value = x match
    case Term.I(v) => Value.I(v)
    case Term.D(v) => Value.D(v)
    case Term.S(v) => Value.T(v)
    case Term.Ap(fn, Nil) => fn.result match
      case okay.proof.Sort.Named(s) => Value.E(s, fn.name)
      case other => throw IllegalStateException(s"a constant of $other")
    case other => throw IllegalStateException(s"not a value: $other")

  private def isValue(x: Term): Boolean = x match
    case Term.I(_) | Term.D(_) | Term.S(_) => true
    case Term.Ap(fn, Nil) => true
    case _ => false

  /** an innermost fact term of a formula: a fact applied to values only */
  private def innermost(f: Formula): Option[Term.Ap] =
    def term(x: Term): Option[Term.Ap] = x match
      case ap @ Term.Ap(fn, as) =>
        as.iterator.flatMap(term).nextOption().orElse(Option.when(t.isFact(fn) && as.forall(isValue))(ap))
      case _ => None
    def go(g: Formula): Option[Term.Ap] = g match
      case F.Eq(a, b) => term(a).orElse(term(b))
      case F.Lt(a, b) => term(a).orElse(term(b))
      case F.Le(a, b) => term(a).orElse(term(b))
      case F.P(_, as) => as.iterator.flatMap(term).nextOption()
      case F.Not(a) => go(a)
      case F.And(a, b) => go(a).orElse(go(b))
      case F.Or(a, b) => go(a).orElse(go(b))
      case F.Imp(a, b) => go(a).orElse(go(b))
      case _ => None
    go(f)

  /** `f` with every occurrence of the term `ft` replaced by `by` */
  private def replace(f: Formula, ft: Term, by: Term): Formula =
    def term(x: Term): Term = if x == ft then by else x match
      case Term.Ap(fn, as) => Term.Ap(fn, as.map(term))
      case other => other
    def go(g: Formula): Formula = g match
      case F.Eq(a, b) => F.Eq(term(a), term(b))
      case F.Lt(a, b) => F.Lt(term(a), term(b))
      case F.Le(a, b) => F.Le(term(a), term(b))
      case F.P(p, as) => F.P(p, as.map(term))
      case F.Not(a) => F.Not(go(a))
      case F.And(a, b) => F.And(go(a), go(b))
      case F.Or(a, b) => F.Or(go(a), go(b))
      case F.Imp(a, b) => F.Imp(go(a), go(b))
      case other => other
    go(f)

  /**
   * an atom, closed but for its facts: each innermost fact replaced by its value, again and again, down to a formula
   * of values (`account(call)` by `acc1`, then `balance(acc1)` by `300`); that one proved — computed, or a relation
   * the guard knows assumed — and each step taken back by `Subst` with its fact's equation reversed, the last first
   */
  private def atom[R[_]: Has[Infer]](f: Formula, known: Known): Thm ! R =
    val steps = scala.collection.mutable.ListBuffer.empty[(Formula, Term.V, Term, Term)] // template, x, fact, value
    var g = f
    var n = 0
    var stuck: Option[String] = None
    while stuck.isEmpty && innermost(g).isDefined do
      val ft = innermost(g).get
      valueOf(ft.fn, ft.args, known) match
        case None => stuck = Some(s"no value of $ft")
        case Some(v) =>
          val x = Term.V(s"§$n", Logic.sortOf(ft).get)
          n += 1
          val template = replace(g, ft, x)
          steps += ((template, x, ft, v))
          g = Logic.subst(template, x, v)
    stuck match
      case Some(why) => Infer.refuse[R](why)
      case None =>
        steps.reverseIterator.foldLeft(closed[R](g)) { case (p, (template, x, ft, v)) =>
          for
            th <- p
            eq <- reversed[R](ft, v)
            next <- Infer.subst[R](eq, x, template, th)
          yield next
        }

  /** `v = fact`, from the fact's equation `fact = v`, assumed: what the guard knows of it */
  private def reversed[R[_]: Has[Infer]](fact: Term, v: Term): Thm ! R =
    val x = Term.V("§=", Logic.sortOf(fact).get)
    for
      eq <- Infer.assume[R](F.Eq(fact, v))
      refl <- Infer.refl[R](fact)
      back <- Infer.subst[R](eq, x, F.Eq(x, fact), refl)
    yield back

  /** a closed formula with no fact in it: computed, or equal names by reflexivity, or by its parts */
  private def closed[R[_]: Has[Infer]](f: Formula): Thm ! R =
    if Arithmetic.truth(f).contains(true) then Infer.compute[R](f)
    else f match
      case F.Eq(a, b) if a == b => Infer.refl[R](a)
      case F.Or(a, b) =>
        if provable(a) then closed[R](a).flatMap(x => Infer.step[R](Rule.OrI1(x, b)))
        else closed[R](b).flatMap(y => Infer.step[R](Rule.OrI2(a, y)))
      case F.And(a, b) => for x <- closed[R](a); y <- closed[R](b); t <- Infer.andI[R](x, y) yield t
      // a relation of values the guard knows (the evaluator read it true, or false under `not`): a hypothesis
      case F.P(_, _) | F.Not(F.P(_, _)) => Infer.assume[R](f)
      case _ => Infer.refuse[R](s"not provable by computation: $f")

  private def provable(f: Formula): Boolean =
    Arithmetic.truth(f).contains(true) || (f match
      case F.Eq(a, b) => a == b
      case F.Or(a, b) => provable(a) || provable(b)
      case F.And(a, b) => provable(a) && provable(b)
      case _ => false)
