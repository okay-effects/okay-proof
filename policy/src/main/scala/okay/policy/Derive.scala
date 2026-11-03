package okay.policy

import okay.datalog as dl
import okay.proof.{Fn, Formula, Infer, Pred, Sort, Term, Theory, Thm}
import okay.proof.Formula as F
import okay.scala3.*

/**
 * DERIVED RELATIONS, CERTIFIED (specs/policy.md, "Derived relations"): a Datalog program over relation facts,
 * computed by okay-datalog — fast, outside the trusted base — and every step a derivation used re-derived in the
 * kernel: the rule's axiom, `∀` out with the variables' values, the premises joined as the body is nested, `ImpE`.
 * Untrusted, like `Prove`: a wrong step is refused by the kernel, so a bug here can make a proof fail, never prove a
 * wrong theorem.
 *
 * `sorts` gives each predicate's argument sorts (an entity sort's values are its constants, as a policy's are);
 * rules are positive (relation atoms only) for now.
 */
final class Derive(val name: String, val program: dl.Program, val sorts: Map[String, List[Sort]]):

  private val rules: Vector[dl.Rule] = program.rules.filter(_.body.nonEmpty)

  for r <- rules; l <- r.body do l match
    case dl.Literal.Pos(_) => ()
    case other => throw IllegalArgumentException(s"a derived relation's rule is positive for now: $other in $r")
  for r <- program.rules; a <- r.head +: r.body.collect { case dl.Literal.Pos(a) => a } do
    val s = sorts.getOrElse(a.pred, throw IllegalArgumentException(s"no sorts for ${a.pred}"))
    if s.size != a.arity then throw IllegalArgumentException(s"${a.pred} has ${s.size} sorts, used with ${a.arity}")

  def pred(p: String): Pred = Pred(p, sorts(p))

  /** a value of a sort, as a policy's values are terms: an entity a constant of its sort, a text a text */
  def constant(v: String, s: Sort): Term = s match
    case Sort.Named(_) => Term.Ap(Fn(v, Nil, s), Nil)
    case Sort.Str => Term.S(v)
    case Sort.Int => Term.I(BigInt(v))
    case Sort.Dec => Term.D(BigDecimal(v))

  /** a ground fact as a formula: `in_group(ann, devs)` */
  def formula(f: dl.Fact): Formula = F.P(pred(f.pred), f.args.zip(sorts(f.pred)).map(constant).toList)

  /** a rule as an axiom: its variables (the head's first), their sorts from where they occur, its formula */
  final case class Axiom(name: String, rule: dl.Rule, vars: List[Term.V], formula: Formula)

  val axioms: Vector[Axiom] = rules.zipWithIndex.map { (r, i) =>
    val atoms = r.body.collect { case dl.Literal.Pos(a) => a }
    val occurrences = (r.head +: atoms).flatMap(a => a.args.zip(sorts(a.pred)).collect {
      case (dl.Term.Var(v), s) => v -> s })
    val sortOf = occurrences.groupMap(_._1)(_._2).map { (v, ss) =>
      if ss.distinct.size > 1 then throw IllegalArgumentException(s"$v is of sorts ${ss.distinct.mkString(", ")} in $r")
      v -> ss.head }
    val vars = (r.head.vars ++ atoms.flatMap(_.vars)).distinct.map(v => Term.V(v, sortOf(v))).toList
    def atom(a: dl.Atom): Formula = F.P(pred(a.pred), a.args.zip(sorts(a.pred)).map {
      case (dl.Term.Var(v), s) => Term.V(v, s)
      case (dl.Term.Const(c), s) => constant(c, s)
    }.toList)
    val body = atoms.map(atom).reduceRight(F.And(_, _))
    Axiom(s"derive ${r.head.pred} ${i + 1}: $r", r, vars, Formula.all(vars*)(F.Imp(body, atom(r.head))))
  }

  private val axiomOf: Map[dl.Rule, Axiom] = axioms.map(a => a.rule -> a).toMap

  /** the rules as a theory's axioms: the policy's theory takes them beside its own */
  def axiomPairs: Vector[(String, Formula)] = axioms.map(a => a.name -> a.formula)
  def theory: Theory = Theory(name, axiomPairs*)

  /** the relations computed over the tables (the base relations given whole), each derivation recorded */
  def run(tables: Iterable[dl.Fact]): Either[String, dl.Result] = dl.Eval.run(program, tables, proofs = true)

  /**
   * The theorem of a derived fact: its derivation's steps, premises first, each fact proved once — a given one
   * assumed (a hypothesis: what the guard was told), a derived one by its rule's axiom. The theorem's hypotheses are
   * exactly the given facts the derivation used.
   */
  def prove[R[_]: Has[Infer]](result: dl.Result, fact: dl.Fact): Thm ! R =
    result.proof(fact) match
      case None => Infer.refuse[R](s"$fact is not derived")
      case Some(steps) =>
        steps.foldLeft(pure[Map[dl.Fact, Thm], R](Map.empty)) { (acc, step) =>
          acc.flatMap(proved => this.step[R](step, proved).map(t => proved.updated(step.fact, t)))
        }.flatMap(proved => proved.get(fact).fold(Infer.refuse[R](s"$fact: no step proves it"))(pure(_)))

  private def step[R[_]: Has[Infer]](s: dl.Step, proved: Map[dl.Fact, Thm]): Thm ! R = s.by match
    case None => Infer.assume[R](formula(s.fact))
    case Some(d) => axiomOf.get(d.rule) match
      case None => Infer.refuse[R](s"no axiom for ${d.rule}")
      case Some(ax) =>
        val atoms = d.rule.body.collect { case dl.Literal.Pos(a) => a }
        // the variables' values: from the head and the premises, each atom matched with its fact
        val pairs = (d.rule.head -> s.fact) +: atoms.zip(d.premises)
        val binding = pairs.flatMap((a, f) => a.args.zip(f.args).collect { case (dl.Term.Var(v), x) => v -> x }).toMap
        val premises = d.premises.map(proved.get)
        if premises.exists(_.isEmpty) then Infer.refuse[R](s"a premise of ${s.fact} not proved before it")
        else
          val start = Infer.axiom[R](ax.name)
          val instance = ax.vars.foldLeft(start)((p, v) =>
            p.flatMap(t => Infer.allE[R](t, constant(binding(v.name), v.sort))))
          for
            imp <- instance
            body <- joined[R](premises.flatten.toList)
            thm <- Infer.impE[R](imp, body)
          yield thm

  /** the premises joined as the body is nested: `a ∧ (b ∧ c)` */
  private def joined[R[_]: Has[Infer]](ts: List[Thm]): Thm ! R = ts match
    case Nil => Infer.refuse[R]("a rule with no premise")
    case List(t) => pure(t)
    case t :: rest => joined[R](rest).flatMap(r => Infer.andI[R](t, r))

object Derive:
  /** a policy's value as okay-datalog's constant: an entity its name, a text itself, a number its digits */
  def text(v: Value): String = v match
    case Value.E(_, n) => n
    case Value.T(t) => t
    case Value.I(i) => i.toString
    case Value.D(d) => d.bigDecimal.toPlainString

  /** a term of a value as okay-datalog's constant: the inverse of `Derive.constant` */
  def text(t: Term): String = t match
    case Term.Ap(fn, Nil) => fn.name
    case Term.S(s) => s
    case Term.I(i) => i.toString
    case Term.D(d) => d.bigDecimal.toPlainString
    case other => throw IllegalArgumentException(s"not a value: $other")
