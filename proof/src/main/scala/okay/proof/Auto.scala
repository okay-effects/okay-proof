package okay.proof

import okay.scala3.*
import okay.scala3.std.*

/**
 * PROOF SEARCH ON EFFECTS: a goal proved backward from FACTS (the hypotheses: what a request brings — roles,
 * amounts, balances) and the theory's RULES (its axioms `∀x̄. body → head`, or `∀x̄. head`: policies, definitions).
 * Each inference a step of `Infer`, so the kernel checks it and any interceptor sees it; each alternative a choice of
 * `Choose`, so the handler is the strategy — `first`, the first proof depth first; `all`, every proof.
 *
 * A goal is, in turn: a fact (`assume`); computable (`compute`, exact arithmetic in one step); a conjunction (both
 * proved); a disjunction (a side chosen); a comparison over `Int` or `Dec` that follows linearly from the facts
 * (`Linarith`: `spent(ann) ≤ 300` and `daily(teller) = 1500` give `spent(ann) + 500 ≤ daily(teller)`); a formula with
 * a term of one's own whose value a fact gives (rewritten, then proved); the head of a rule (its variables bound by the head, the rest by facts matching
 * its body, the body then proved). Nothing here is trusted: a wrong step is refused by the kernel.
 */
final class Auto(theory: Theory, facts: List[Formula], depth: Int = 32):
  import Formula.*
  import Term.*
  import Infer.*

  private final case class RuleShape(name: String, vars: List[V], body: Option[Formula], head: Formula)

  private val rules: List[RuleShape] = theory.axioms.toList.sortBy(_._1).map { (n, f) =>
    def strip(g: Formula, xs: List[V]): (List[V], Formula) = g match
      case All(x, h) => strip(h, x :: xs)
      case h => (xs.reverse, h)
    val (xs, m) = strip(f, Nil)
    m match
      case Imp(b, h) => RuleShape(n, xs, Some(b), h)
      case h => RuleShape(n, xs, None, h)
  }

  private val factSet: Set[Formula] = facts.toSet

  /** `goal`, proved — or no branch: a failed choice */
  def prove[R[_]: Has[Infer]: Has[Choose]](goal: Formula): Thm ! R = go[R](goal, depth)

  private def none[R[_]: Has[Choose]]: Thm ! R = Choose.none[Thm, R]

  private def go[R[_]: Has[Infer]: Has[Choose]](goal: Formula, d: Int): Thm ! R =
    if d <= 0 then none[R]
    else if factSet.contains(goal) then assume[R](goal)
    else if goal.free.isEmpty && Arithmetic.truth(goal).isDefined then
      // closed and computable: true in one step, or false — a branch that ends here
      if Arithmetic.truth(goal).contains(true) then compute[R](goal) else none[R]
    else goal match
      case And(a, b) => go[R](a, d - 1).flatMap(ta => go[R](b, d - 1).flatMap(tb => andI[R](ta, tb)))
      case Or(a, b) => Choose.among[Boolean, R](List(true, false)).flatMap { left =>
          if left then go[R](a, d - 1).flatMap(t => step[R](Rule.OrI1(t, b)))
          else go[R](b, d - 1).flatMap(t => step[R](Rule.OrI2(a, t)))
        }
      case _ =>
        // a value a fact gives first (the cheaper proof); then, for a comparison over Int or Dec, linear arithmetic
        // over the facts — a certificate the kernel checks; then the rules
        rewrite(goal) match
          case Some((s, v, eq)) => byRewriting[R](goal, s, v, eq, d)
          case None =>
            Linarith.sortOf(goal).flatMap(_ => Linarith.prove[R](goal, facts)) match
              case Some(proof) => proof
              case None => byRules[R](goal, d)

  /** a ground term of one's own in `goal` whose value a fact gives: the term, the value, the fact */
  private def rewrite(goal: Formula): Option[(Term, Term, Formula)] =
    def terms(f: Formula): List[Term] = f match
      case Eq(a, b) => sub(a) ++ sub(b)
      case Lt(a, b) => sub(a) ++ sub(b)
      case Le(a, b) => sub(a) ++ sub(b)
      case P(_, as) => as.flatMap(sub)
      case Not(g) => terms(g)
      case _ => Nil
    def sub(t: Term): List[Term] = t match
      case Ap(fn, as) => (if !Fns.all.contains(fn) && t.free.isEmpty then List(t) else Nil) ++ as.flatMap(sub)
      case _ => Nil
    terms(goal).iterator.flatMap { s =>
      facts.iterator.collect {
        case f @ Eq(`s`, v) if v != s && Arithmetic.value(v).isDefined => (s, v, f)
      }
    }.nextOption()

  /** `goal` with `s` its value `v`, proved; then `s` put back by the fact `s = v` */
  private def byRewriting[R[_]: Has[Infer]: Has[Choose]](goal: Formula, s: Term, v: Term, fact: Formula, d: Int)
      : Thm ! R =
    val sort = Logic.sortOf(s).get
    val x = Logic.fresh(V("x", sort), goal.free)
    val shape = abstractTerm(goal, s, x)
    val y = Logic.fresh(V("y", sort), s.free + x)
    for
      inst <- go[R](Logic.subst(shape, x, v), d - 1)
      eq <- assume[R](fact)
      self <- refl[R](s)
      back <- subst[R](eq, y, Eq(y, s), self) // s = v ⊢ v = s
      t <- subst[R](back, x, shape, inst)
    yield t

  private def abstractTerm(f: Formula, s: Term, x: V): Formula =
    def t(u: Term): Term = if u == s then x else u match
      case Ap(fn, as) => Ap(fn, as.map(t))
      case other => other
    f match
      case Eq(a, b) => Eq(t(a), t(b))
      case Lt(a, b) => Lt(t(a), t(b))
      case Le(a, b) => Le(t(a), t(b))
      case P(p, as) => P(p, as.map(t))
      case Not(g) => Not(abstractTerm(g, s, x))
      case other => other

  /** `goal` as the head of a rule, chosen among those whose head matches */
  private def byRules[R[_]: Has[Infer]: Has[Choose]](goal: Formula, d: Int): Thm ! R =
    val candidates = rules.flatMap(r => Auto.matchF(r.head, goal, r.vars.toSet, Map.empty).map(r -> _))
    Choose.among[(RuleShape, Map[V, Term]), R](candidates).flatMap { (r, bound) =>
      r.body match
        case None => instantiate[R](r, bound)
        case Some(body) =>
          bindFromFacts[R](conjuncts(body), r.vars.toSet, bound).flatMap { b =>
            if !r.vars.forall(b.contains) then none[R]
            else
              val inst = r.vars.foldLeft(body)((f, x) => Logic.subst(f, x, b(x)))
              for
                imp <- instantiate[R](r, b)
                arg <- go[R](inst, d - 1)
                t <- impE[R](imp, arg)
              yield t
          }
    }

  private def instantiate[R[_]: Has[Infer]: Has[Choose]](r: RuleShape, b: Map[V, Term]): Thm ! R =
    if !r.vars.forall(b.contains) then none[R]
    else r.vars.foldLeft(axiom[R](r.name))((p, x) => p.flatMap(t => allE[R](t, b(x))))

  private def conjuncts(f: Formula): List[Formula] = f match
    case And(a, b) => conjuncts(a) ++ conjuncts(b)
    case g => List(g)

  /** the rule's variables the head left unbound, bound by facts matching its body's conjuncts — a choice each */
  private def bindFromFacts[R[_]: Has[Choose]](cs: List[Formula], vars: Set[V], b: Map[V, Term])
      : Map[V, Term] ! R = cs match
    case Nil => pure(b)
    case c :: rest =>
      val open = c.free.intersect(vars).exists(x => !b.contains(x))
      if !open then bindFromFacts[R](rest, vars, b)
      else
        val options = facts.flatMap(f => Auto.matchF(c, f, vars, b))
        Choose.among[Map[V, Term], R](options).flatMap(b2 => bindFromFacts[R](rest, vars, b2))

object Auto:
  import Formula.*
  import Term.*

  /** `p`'s variables `vars` bound so that `p` is `t`, extending `b` */
  def matchT(p: Term, t: Term, vars: Set[V], b: Map[V, Term]): Option[Map[V, Term]] = (p, t) match
    case (x: V, _) if vars.contains(x) => b.get(x) match
      case Some(u) => Option.when(u == t)(b)
      case None => Option.when(Logic.sortOf(t).contains(x.sort))(b + (x -> t))
    case (Ap(f, as), Ap(g, bs)) if f == g && as.length == bs.length => matchAll(as, bs, vars, b)
    case _ => Option.when(p == t)(b)

  private def matchAll(ps: List[Term], ts: List[Term], vars: Set[V], b: Map[V, Term]): Option[Map[V, Term]] =
    ps.lazyZip(ts).foldLeft(Option(b)) { case (acc, (p, t)) => acc.flatMap(matchT(p, t, vars, _)) }

  def matchF(p: Formula, f: Formula, vars: Set[V], b: Map[V, Term]): Option[Map[V, Term]] = (p, f) match
    case (Eq(a, c), Eq(x, y)) => matchT(a, x, vars, b).flatMap(matchT(c, y, vars, _))
    case (Lt(a, c), Lt(x, y)) => matchT(a, x, vars, b).flatMap(matchT(c, y, vars, _))
    case (Le(a, c), Le(x, y)) => matchT(a, x, vars, b).flatMap(matchT(c, y, vars, _))
    case (P(q, as), P(r, bs)) if q == r => matchAll(as, bs, vars, b)
    case (Not(g), Not(h)) => matchF(g, h, vars, b)
    case _ => Option.when(p == f)(b)

  /** `goal` from `facts` under `kernel`'s theory: the first proof, depth first — `Right(None)` if there is none; a
   * refused step `Left` */
  def prove(kernel: Kernel, facts: List[Formula], goal: Formula, depth: Int = 32): Either[String, Option[Thm]] =
    val search = Auto(kernel.theory, facts, depth)
    run(Infer.checking(kernel)(Choose.first(search.prove[Infer + Choose](goal)))) match
      case Right(Some(t)) if !kernel.owns(t) => Left(s"a theorem of another kernel: ${t.concl}")
      case other => other
