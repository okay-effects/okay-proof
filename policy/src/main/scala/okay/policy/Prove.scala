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
    case TExpr.Var(n, _) => TExpr.Lit(env(n))
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

  /** the theorem that `rule` decides `call`: its condition holding under `known` (checked by the evaluator first) */
  def decision[R[_]: Has[Infer]](rule: TRule, call: Call, known: Known): Thm ! R =
    val env = call.env
    val vars = t.vars(call.tool)
    val values = vars.map(v => t.term(env(v.name)))
    val axiom = Infer.axiom[R](t.axiomName(rule, call.tool))
    val instance = values.foldLeft(axiom)((p, v) => p.flatMap(th => Infer.allE[R](th, v)))
    rule.when match
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
    case TCond.Holds(_, _) => Infer.assume[R](t.formula(c))
    case TCond.Not(TCond.Holds(_, _)) => Infer.assume[R](t.formula(c))
    case _ => atom[R](t.formula(c), known)

  /** the fact terms of a formula with their values: each a function fact or a state applied to constants */
  private def factTerms(f: Formula, known: Known): List[(Term, Term)] =
    val found = scala.collection.mutable.LinkedHashMap.empty[Term, Term]
    def term(x: Term): Unit = x match
      case ap @ Term.Ap(fn, as) if t.factFns.get(fn.name).contains(fn) =>
        if !found.contains(ap) then found(ap) = valueOf(fn.name, as, known)
      case Term.Ap(_, as) => as.foreach(term)
      case _ => ()
    def formula(g: Formula): Unit = g match
      case F.Eq(a, b) => term(a); term(b)
      case F.Lt(a, b) => term(a); term(b)
      case F.Le(a, b) => term(a); term(b)
      case F.P(_, as) => as.foreach(term)
      case F.Not(a) => formula(a)
      case F.And(a, b) => formula(a); formula(b)
      case F.Or(a, b) => formula(a); formula(b)
      case F.Imp(a, b) => formula(a); formula(b)
      case _ => ()
    formula(f)
    found.toList

  /** a fact's or a state's value as a term, read back from what is known by its ground arguments */
  private def valueOf(name: String, args: List[Term], known: Known): Term =
    val key = FactRef(name, args.map(valueOfTerm))
    known.facts.get(key) match
      case Some(Answer.Is(v)) => t.term(v)
      case _ => known.states.get(key) match
        case Some(v) => t.term(v)
        case None => throw IllegalStateException(s"no value of $key")

  private def valueOfTerm(x: Term): Value = x match
    case Term.I(v) => Value.I(v)
    case Term.D(v) => Value.D(v)
    case Term.S(v) => Value.T(v)
    case Term.Ap(fn, Nil) => fn.result match
      case okay.proof.Sort.Named(s) => Value.E(s, fn.name)
      case other => throw IllegalStateException(s"a constant of $other")
    case other => throw IllegalStateException(s"not a value: $other")

  /** each ground fact term replaced by a variable of its own */
  private def abstractTerms(f: Formula, ts: List[(Term, Term.V)]): Formula =
    def term(x: Term): Term = ts.find(_._1 == x) match
      case Some((_, v)) => v
      case None => x match
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

  /** an atom, closed but for its facts: computed with their values, then each value turned back into its fact */
  private def atom[R[_]: Has[Infer]](f: Formula, known: Known): Thm ! R =
    val facts = factTerms(f, known)
    val xs = facts.zipWithIndex.map { case ((ft, _), i) => (ft, Term.V(s"§$i", Logic.sortOf(ft).get)) }
    val g = abstractTerms(f, xs)
    val values = facts.map(_._2)
    val vars = xs.map(_._2)
    def withValues(from: Int): Formula = // g with the facts before `from` in place, the values from it on
      vars.zipWithIndex.foldLeft(g) { case (h, (x, i)) =>
        Logic.subst(h, x, if i < from then facts(i)._1 else values(i))
      }
    val start = closed[R](withValues(0))
    facts.indices.foldLeft(start) { (p, i) =>
      // f_i: the facts before i in place, x_i free, the values after it
      val fi = vars.zipWithIndex.foldLeft(g) { case (h, (x, j)) =>
        if j == i then h else Logic.subst(h, x, if j < i then facts(j)._1 else values(j))
      }
      for
        th <- p
        eq <- reversed[R](facts(i)._1, values(i))
        next <- Infer.subst[R](eq, vars(i), fi, th)
      yield next
    }

  /** `v = fact`, from the fact's equation `fact = v`, assumed */
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
      case _ => Infer.refuse[R](s"not provable by computation: $f")

  private def provable(f: Formula): Boolean =
    Arithmetic.truth(f).contains(true) || (f match
      case F.Eq(a, b) => a == b
      case F.Or(a, b) => provable(a) || provable(b)
      case F.And(a, b) => provable(a) && provable(b)
      case _ => false)
