package okay.policy

import scala.collection.mutable.ArrayBuffer

/** a value at run time: a number, a text, an entity's name */
enum Value:
  case I(v: BigInt)
  case D(v: BigDecimal)
  case T(v: String)
  case E(sort: String, name: String)

  override def toString: String = this match
    case I(v) => v.toString
    case D(v) => v.bigDecimal.toPlainString
    case T(v) => Printer.quote(v)
    case E(_, n) => n

/** A CHECKED EXPRESSION: every sort known, names resolved */
enum TExpr:
  case Lit(v: Value)
  /** `caller`, `tool`, or an argument of the call */
  case Var(name: String, of: Sort)
  /** a function fact applied, or a state read: its arguments variables or literals */
  case Fact(name: String, args: List[TExpr], of: Sort)
  case State(name: String, args: List[TExpr], of: Sort)
  case Add(a: TExpr, b: TExpr, of: Sort)
  case Sub(a: TExpr, b: TExpr, of: Sort)
  /** a product by a literal: the conditions stay linear */
  case Mul(a: TExpr, by: Value, of: Sort)
  /** an `Int` as a `Dec` */
  case ToDec(a: TExpr)

  def sort: Sort = this match
    case Lit(v) => v match
      case Value.I(_) => Sort.Int
      case Value.D(_) => Sort.Dec
      case Value.T(_) => Sort.Text
      case Value.E(s, _) => Sort.Entity(s)
    case Var(_, s) => s
    case Fact(_, _, s) => s
    case State(_, _, s) => s
    case Add(_, _, s) => s
    case Sub(_, _, s) => s
    case Mul(_, _, s) => s
    case ToDec(_) => Sort.Dec

/** a list in a condition: its membership predicate's name, what it belongs to (the call, or an element), its
 * elements' sort */
final case class TList(name: String, base: TExpr, elem: Sort)

/** A CHECKED CONDITION */
enum TCond:
  case Compare(a: TExpr, cmp: Cmp, b: TExpr)
  case In(a: TExpr, options: List[TExpr])
  case Holds(name: String, args: List[TExpr])
  case Text(a: TExpr, op: TextOp, b: TExpr)
  case And(a: TCond, b: TCond)
  case Or(a: TCond, b: TCond)
  case Not(c: TCond)
  /** each element of a list: `∀x. list(base, x) ⇒ body` */
  case Every(x: String, list: TList, body: TCond)
  /** one of them: `∃x. list(base, x) ∧ body` */
  case Exists(x: String, list: TList, body: TCond)

final case class TUpdate(state: String, key: List[TExpr], change: Change, value: TExpr)

final case class FactSig(name: String, params: List[Sort], result: Option[Sort], source: Option[String],
                         fetch: Option[TFetch] = None)

/** a fact's fetch checked: the tool, its arguments over the fact's parameters (by their names), the path */
final case class TFetch(tool: String, params: List[String], args: List[(String, TExpr)], at: List[String])
final case class StateSig(name: String, params: List[Sort], sort: Sort, window: Option[Window], init: Value)
/** an argument of a call, or a field of a record: its sort, and whether it may be missing */
final case class Field(name: String, sort: Sort, optional: Boolean)
final case class CallSig(tool: String, params: List[Field], reads: Boolean = false)

/** a rule checked: the tools it decides, its condition and updates over their common variables */
final case class TRule(index: Int, verdict: Verdict, tools: List[String], when: Option[TCond], updates: List[TUpdate],
                       because: Option[String], source: Decl.Rule)

/** a count checked: the tools whose calls it counts, its condition, its updates */
final case class TCount(tools: List[String], when: Option[TCond], updates: List[TUpdate], source: Decl.Count)

final case class TGiven(name: String, args: List[Value], value: Either[Boolean, Value])
final case class TTest(name: String, givens: List[TGiven], caller: Value, tool: String, args: Map[String, Data],
                       expect: Verdict, because: Option[String], source: Decl.Test)

/** a notice checked: the webhooks it goes to, on what outcome, of which tools' calls, when */
final case class TNotice(names: List[String], on: NoticeOn, tools: List[String], when: Option[TCond],
                         source: Decl.Notify)

/** A POLICY CHECKED: its signatures, and its rules and tests over them — what the evaluator runs; its default verdict
 * (deny unless said), its webhooks and its notices — the guard's to act on */
final case class Checked(policy: Policy, types: Set[String], records: Map[String, List[Field]],
                         facts: Map[String, FactSig], states: Map[String, StateSig], calls: Map[String, CallSig],
                         rules: List[TRule], counts: List[TCount], default: Verdict = Verdict.Deny,
                         webhooks: Map[String, Hook] = Map.empty, notices: List[TNotice] = Nil):
  /** the rules deciding `tool`, in the policy's order */
  lazy val rulesOf: Map[String, List[TRule]] = calls.keys.map(t => t -> rules.filter(_.tools.contains(t))).toMap
  /** the counts of `tool`'s calls */
  lazy val countsOf: Map[String, List[TCount]] = calls.keys.map(t => t -> counts.filter(_.tools.contains(t))).toMap

  /** a target covers a tool: `*` every one, `server.*` its server's, a tool itself */
  def covers(target: Target, tool: String): Boolean = target match
    case Target.Any => true
    case Target.Server(s) => tool.startsWith(s + ".")
    case Target.Tool(t) => t == tool

  /** a target that covers tools the policy does not declare */
  def open(target: Target): Boolean = !target.isInstanceOf[Target.Tool]

  /** the rules deciding `tool`: a declared one's; an undeclared one's — the open rules (`*`, `server.*`) covering it */
  def rulesFor(tool: String): List[TRule] =
    rulesOf.getOrElse(tool, rules.filter(r => open(r.source.target) && covers(r.source.target, tool)))

  def countsFor(tool: String): List[TCount] =
    countsOf.getOrElse(tool, counts.filter(c => open(c.source.target) && covers(c.source.target, tool)))

/** THE TYPE CHECKER: every problem of a policy, each with its place — or the policy checked */
object Types:
  /** the sort of `caller`: a policy that uses it declares `type User` */
  val callerType = "User"
  /** the sort of the call itself, an entity of the logic: its arguments are facts about it */
  val callType = "Call"
  val call: TExpr = TExpr.Var("call", Sort.Entity(callType))

  def check(p: Policy): Either[List[Problem], Checked] = Checking(p).run()

  /** a condition with its negations on atoms alone (`not (a and b)` is `not a or not b`): what a decision's proof
   * can take apart — the policy means the same */
  def nnf(c: TCond): TCond = c match
    case TCond.And(a, b) => TCond.And(nnf(a), nnf(b))
    case TCond.Or(a, b) => TCond.Or(nnf(a), nnf(b))
    case TCond.Not(TCond.Not(a)) => nnf(a)
    case TCond.Not(TCond.And(a, b)) => TCond.Or(nnf(TCond.Not(a)), nnf(TCond.Not(b)))
    case TCond.Not(TCond.Or(a, b)) => TCond.And(nnf(TCond.Not(a)), nnf(TCond.Not(b)))
    case TCond.Not(TCond.Every(x, l, b)) => TCond.Exists(x, l, nnf(TCond.Not(b)))
    case TCond.Not(TCond.Exists(x, l, b)) => TCond.Every(x, l, nnf(TCond.Not(b)))
    case TCond.Every(x, l, b) => TCond.Every(x, l, nnf(b))
    case TCond.Exists(x, l, b) => TCond.Exists(x, l, nnf(b))
    case other => other

  /** the text parsed and checked: the parser's problem, or the checker's */
  def apply(text: String): Either[List[Problem], Checked] = Parser.parse(text).left.map(List(_)).flatMap(check)

  /** a file of tests checked against its policy: its tests, or every problem */
  def tests(c: Checked, f: TestFile): Either[List[Problem], List[TTest]] = Checking(c.policy).tests(c, f)

  /** a file of tests' text, parsed and checked against the policy */
  def tests(c: Checked, text: String): Either[List[Problem], List[TTest]] =
    Parser.parseTests(text).left.map(List(_)).flatMap(tests(c, _))

  private final class Checking(p: Policy):
    private val problems = ArrayBuffer.empty[Problem]
    private def problem(pos: Pos, message: String): Unit = problems += Problem(pos, message)

    private val types: Set[String] = p.types.map(_.name).toSet
    private val recordNames: Set[String] = p.records.map(_.name).toSet
    /** a sort as written, a record's name made a record */
    private def norm(s: Sort): Sort = s match
      case Sort.Entity(n) if recordNames(n) => Sort.Rec(n)
      case Sort.ListOf(e) => Sort.ListOf(norm(e))
      case other => other
    private def known(s: Sort, pos: Pos): Boolean = s match
      case Sort.ListOf(Sort.Bool) => problem(pos, "a list of Bool: not yet"); false
      case Sort.Entity(n) if !types(n) && !recordNames(n) => problem(pos, s"an unknown type $n"); false
      case Sort.ListOf(e) => known(e, pos)
      case _ => true
    /** a fact's or a state's parameters and values: no records, no lists */
    private def flat(s: Sort, pos: Pos, what: String): Unit = norm(s) match
      case Sort.Rec(_) | Sort.ListOf(_) | Sort.Bool => problem(pos, s"$what is a number, a text or an entity, not $s" +
        (if s == Sort.Bool then " (a relation fact is what is true or not)" else ""))
      case _ => ()
    private val records: Map[String, List[Field]] =
      p.records.map(r => r.name -> r.fields.map(f => Field(f.name, norm(f.sort), f.optional))).toMap

    def run(): Either[List[Problem], Checked] =
      duplicates(p.types.map(t => (t.name, t.pos)) ++ p.records.map(r => (r.name, r.pos)), "type")
      (p.types.map(t => (t.name, t.pos)) ++ p.records.map(r => (r.name, r.pos))).find(_._1 == callType)
        .foreach((_, pos) => problem(pos, s"`$callType` is the call's own type"))
      p.records.foreach { r =>
        duplicates(r.fields.map(f => (f.name, f.pos)), "field")
        r.fields.foreach(f => known(f.sort, f.pos))
      }
      duplicates((p.facts.map(f => (f.name, f.pos)) ++ p.states.map(s => (s.name, s.pos))), "fact or state")
      duplicates(p.calls.map(c => (c.tool, c.pos)), "call")
      val facts = p.facts.map { f =>
        f.params.foreach(x => { known(x.sort, x.pos); flat(x.sort, x.pos, s"a fact's parameter ${x.name}") })
        f.result.foreach(r => { known(r, f.pos); flat(r, f.pos, s"${f.name}'s value") })
        duplicates(f.params.map(x => (x.name, x.pos)), "parameter")
        val fetch = f.fetch.flatMap { fe =>
          val scope = Scope(f.params.map(x => x.name -> norm(x.sort)).toMap, Map.empty,
            Sigs(Map.empty, Map.empty, Map.empty, Map.empty), Target.Any, Nil)
          val as = fe.args.map((k, v) => k -> expr(v, scope, None))
          if fe.at.isEmpty then problem(fe.pos, "a path in the tool's result: \"\" names nothing")
          Option.when(as.forall(_._2.isDefined) && fe.at.nonEmpty)(
            TFetch(fe.tool, f.params.map(_.name), as.map((k, v) => k -> v.get), fe.at.split('.').toList))
        }
        f.name -> FactSig(f.name, f.params.map(_.sort), f.result, f.source, fetch)
      }.toMap
      val states = p.states.flatMap { s =>
        s.params.foreach(x => { known(x.sort, x.pos); flat(x.sort, x.pos, s"a state's key ${x.name}") })
        known(s.sort, s.pos)
        if s.sort == Sort.Text || s.sort.isInstanceOf[Sort.Entity] then
          problem(s.pos, s"a state is a number: ${s.name} is ${s.sort}")
        literal(s.init, s.sort).map(v => s.name -> StateSig(s.name, s.params.map(_.sort), s.sort, s.window, v))
      }.toMap
      val calls = p.calls.map { c =>
        c.params.foreach(x => known(x.sort, x.pos))
        duplicates(c.params.map(x => (x.name, x.pos)), "argument")
        c.params.find(x => x.name == "caller" || x.name == "tool" || x.name == "call")
          .foreach(x => problem(x.pos, s"`${x.name}` is every call's own: not an argument"))
        c.tool -> CallSig(c.tool, c.params.map(x => Field(x.name, norm(x.sort), x.optional)), c.reads)
      }.toMap
      val sigs = Sigs(facts, states, calls, records)
      val rules = p.rules.zipWithIndex.flatMap((r, i) => rule(r, i, sigs))
      val counts = p.counts.flatMap(count(_, sigs))
      p.defaults.drop(1).foreach(d => problem(d.pos, "a second default: a policy has one"))
      duplicates(p.webhooks.map(w => (w.name, w.pos)), "webhook")
      val hooks = p.webhooks.map(w => w.name -> w.at).toMap
      def declared(names: List[String], pos: Pos): Unit =
        names.filterNot(hooks.contains).foreach(n => problem(pos, s"an unknown webhook $n: declare it with `webhook`"))
      p.rules.foreach(r => declared(r.notifies, r.pos))
      val notices = p.notices.flatMap { n =>
        declared(n.names, n.pos)
        scopeOf(n.target, n.pos, sigs).flatMap { scope =>
          val when = n.when.flatMap(cond(_, scope)).map(nnf)
          Option.when(n.when.isEmpty || when.isDefined)(TNotice(n.names, n.on, scope.tools, when, n))
        }
      }
      val default = p.defaults.headOption.fold(Verdict.Deny)(_.verdict)
      if problems.isEmpty then
        Right(Checked(p, types, records, facts, states, calls, rules, counts, default, hooks, notices))
      else Left(problems.toList.sortBy(q => (q.pos.line, q.pos.col)))

    def tests(c: Checked, f: TestFile): Either[List[Problem], List[TTest]] =
      if f.policy != c.policy.name then problem(f.pos, s"tests for ${f.policy}, not for ${c.policy.name}")
      val sigs = Sigs(c.facts, c.states, c.calls, c.records)
      duplicates(f.tests.map(t => (t.name, t.pos)), "test")
      val out = f.tests.flatMap(test(_, sigs))
      if problems.isEmpty then Right(out) else Left(problems.toList.sortBy(q => (q.pos.line, q.pos.col)))

    private def duplicates(names: List[(String, Pos)], what: String): Unit =
      names.groupBy(_._1).foreach((n, all) =>
        if all.size > 1 then all.sortBy((_, p) => (p.line, p.col)).tail.foreach((_, p) => problem(p,
          s"a $what $n again")))

    private final case class Sigs(facts: Map[String, FactSig], states: Map[String, StateSig],
                                  calls: Map[String, CallSig], records: Map[String, List[Field]])

    /** a literal of the sort, an `Int` one where a `Dec` is wanted */
    private def literal(e: Expr, s: Sort): Option[Value] = (e, s) match
      case (Expr.IntLit(v, _), Sort.Int) => Some(Value.I(v))
      case (Expr.IntLit(v, _), Sort.Dec) => Some(Value.D(BigDecimal(v)))
      case (Expr.DecLit(v, _), Sort.Dec) => Some(Value.D(v))
      case (Expr.TextLit(v, _), Sort.Text) => Some(Value.T(v))
      case (Expr.Var(n, _), Sort.Entity(t)) => Some(Value.E(t, n))
      case _ =>
        problem(e.pos, s"expected a literal of $s, found ${Printer.expr(e)}")
        None

    /** a target's tools, and the scope of a rule or a count on them: `caller`, `tool`, and the arguments every tool
     * has, of one sort; none if a tool is unknown */
    private def scopeOf(target: Target, pos: Pos, sigs: Sigs): Option[Scope] =
      val tools = target match
        case Target.Tool(t) =>
          if !sigs.calls.contains(t) then problem(pos, s"an unknown tool $t: declare it with `call`")
          List(t)
        case Target.Server(s) => sigs.calls.keys.filter(_.startsWith(s + ".")).toList.sorted
        case Target.Any => sigs.calls.keys.toList.sorted
      val common = tools.map(t => sigs.calls.get(t).fold(Map.empty[String,
        Field])(_.params.map(f => f.name -> f).toMap))
      val args = common.headOption.fold(Map.empty[String, Field])(first =>
        first.filter((n, f) => common.forall(_.get(n).exists(_.sort == f.sort))))
      // `*` and `server.*` may cover no declared tool: they decide the undeclared ones too
      Option.when((tools.nonEmpty || !target.isInstanceOf[Target.Tool]) &&
          tools.forall(sigs.calls.contains))(
        Scope(Map("caller" -> Sort.Entity(callerType), "tool" -> Sort.Text), args, sigs, target, tools))

    private def rule(r: Decl.Rule, index: Int, sigs: Sigs): Option[TRule] =
      scopeOf(r.target, r.pos, sigs).flatMap { scope =>
        val when = r.when.flatMap(cond(_, scope)).map(nnf)
        val updates = r.updates.flatMap(update(_, scope))
        Option.when(r.when.isEmpty || when.isDefined)(
          TRule(index, r.verdict, scope.tools, when, updates, r.because, r))
      }

    private def count(c: Decl.Count, sigs: Sigs): Option[TCount] =
      scopeOf(c.target, c.pos, sigs).flatMap { scope =>
        val when = c.when.flatMap(cond(_, scope)).map(nnf)
        val updates = c.updates.flatMap(update(_, scope))
        Option.when(c.when.isEmpty || when.isDefined)(TCount(scope.tools, when, updates, c))
      }

    /** what a rule's expressions may name: variables (`caller`, `tool`, an element bound by `every`/`some`), the
     * arguments its tools have in common, the policy's signatures */
    private final case class Scope(env: Map[String, Sort], args: Map[String, Field], sigs: Sigs, target: Target,
                                   tools: List[String]):
      def bind(x: String, s: Sort): Scope = copy(env = env + (x -> s))
      def missing(name: String, pos: Pos): Unit =
        val inSome = tools.filter(t => sigs.calls.get(t).exists(_.params.exists(_.name == name)))
        if inSome.nonEmpty then
          problem(pos, s"`$name` is not an argument of every tool this rule decides (${target.word}): only of " +
            inSome.mkString(", "))
        else problem(pos, s"an unknown name $name")

    private def update(u: Update, scope: Scope): Option[TUpdate] =
      scope.sigs.states.get(u.state) match
        case None =>
          if scope.sigs.facts.contains(u.state) then problem(u.pos, s"${u.state} is a fact: only a state changes")
          else problem(u.pos, s"an unknown state ${u.state}")
          None
        case Some(sig) =>
          val key = args(u.state, u.key, sig.params, u.pos, scope)
          val value = expr(u.value, scope, Some(sig.sort))
          if u.change != Change.Set && !numeric(sig.sort) then problem(u.pos, s"${u.change.text} on a $sig.sort")
          for k <- key; v <- value; w <- fit(v, sig.sort, u.value.pos) yield TUpdate(u.state, k, u.change, w)

    private def numeric(s: Sort) = s == Sort.Int || s == Sort.Dec

    /** what a path names: a value, a list, or a record (only `has` takes one) */
    private enum Named:
      case Leaf(e: TExpr)
      case Lst(l: TList)
      case Record(name: String, base: TExpr, rec: String)

    /** a path — `amount`, `shipping.country`, `i.price`, `items` — from a variable or an argument, through records'
     * fields: its function's name is the path from its base (`arg:shipping.country` of the call, `Item.price` of an
     * element) */
    private def path(p: String, pos: Pos, scope: Scope): Option[Named] =
      val segs = p.split('.').toList
      val start: Option[(TExpr, String, Sort)] = scope.env.get(segs.head) match
        case Some(Sort.Rec(r)) => Some((TExpr.Var(segs.head, Sort.Rec(r)), r, Sort.Rec(r)))
        case Some(s) => Some((TExpr.Var(segs.head, s), "", s))
        case None => scope.args.get(segs.head).map(f => (call, "arg:" + segs.head, f.sort))
      start match
        case None => scope.missing(segs.head, pos); None
        case Some((base, name0, sort0)) =>
          if segs.tail.isEmpty && base != call then
            sort0 match
              case Sort.Rec(r) => Some(Named.Record(segs.head, base, r))
              case s => Some(Named.Leaf(base))
          else
            // walk the fields; an element's base starts at its record's name
            var name = name0
            var sort = sort0
            var ok = true
            for seg <- segs.tail if ok do
              sort match
                case Sort.Rec(r) => scope.sigs.records(r).find(_.name == seg) match
                  case Some(f) =>
                    name = if name.isEmpty || name == r && base != call then s"$r.$seg" else s"$name.$seg"
                    sort = f.sort
                  case None => problem(pos, s"$r has no field $seg"); ok = false
                case Sort.ListOf(_) =>
                  problem(pos, s"a list's elements are reached by every or some, not by a path: $p"); ok = false
                case other => problem(pos, s"$other has no fields: $p"); ok = false
            if !ok then None
            else sort match
              case Sort.ListOf(e) => Some(Named.Lst(TList(name, base, e)))
              case Sort.Rec(r) => Some(Named.Record(name, base, r))
              case s => Some(Named.Leaf(TExpr.Fact(name, List(base), s)))

    /** `e` as the sort `s`: an `Int` lifted to a `Dec`, else the same sort or a problem */
    private def fit(e: TExpr, s: Sort, pos: Pos): Option[TExpr] =
      if e.sort == s then Some(e)
      else if e.sort == Sort.Int && s == Sort.Dec then Some(e match
        case TExpr.Lit(Value.I(v)) => TExpr.Lit(Value.D(BigDecimal(v)))
        case _ => TExpr.ToDec(e))
      else
        problem(pos, s"expected $s, found ${e.sort}")
        None

    private def args(name: String, as: List[Expr], sorts: List[Sort], pos: Pos, scope: Scope): Option[List[TExpr]] =
      if as.length != sorts.length then
        problem(pos,
          s"$name takes ${sorts.length} argument${if sorts.length == 1 then "" else "s"}, given ${as.length}")
        None
      else
        val checked = as.zip(sorts).map { (a, s) =>
          a match
            case _: Expr.Apply =>
              problem(a.pos, s"a fact's argument is a name or a literal, not a fact: ${Printer.expr(a)}")
              None
            case _ => expr(a, scope, Some(s)).flatMap(fit(_, s, a.pos))
        }
        Option.when(checked.forall(_.isDefined))(checked.flatten)

    /** an expression's checked form; `want`, the sort expected, if known: a name that is no variable is then an entity
     * of that sort (`caller = admin`) */
    private def expr(e: Expr, scope: Scope, want: Option[Sort]): Option[TExpr] = e match
      case Expr.IntLit(v, _) => Some(TExpr.Lit(Value.I(v)))
      case Expr.DecLit(v, _) => Some(TExpr.Lit(Value.D(v)))
      case Expr.TextLit(v, _) => Some(TExpr.Lit(Value.T(v)))
      case Expr.Var(n, pos) =>
        val head = n.takeWhile(_ != '.')
        if scope.env.contains(head) || scope.args.contains(head) then path(n, pos, scope).flatMap {
          case Named.Leaf(t) if t.sort == Sort.Bool =>
            problem(pos, s"$n is a Bool: a condition by itself (`$n`, `not $n`), not a value"); None
          case Named.Leaf(t) => Some(t)
          case Named.Lst(_) => problem(pos, s"$n is a list: count($n), every or some"); None
          case Named.Record(_, _, r) => problem(pos, s"$n is a $r: a field of it, or has($n)"); None
        }
        else want match
          case Some(Sort.Entity(t)) if !n.contains('.') => Some(TExpr.Lit(Value.E(t, n)))
          case _ => scope.missing(head, pos); None
      case Expr.Apply("count", List(Expr.Var(n, vp)), pos) if !scope.sigs.facts.contains("count") =>
        path(n, vp, scope).flatMap {
          case Named.Lst(l) => Some(TExpr.Fact(l.name + "#count", List(l.base), Sort.Int))
          case _ => problem(pos, s"count of a list only: $n"); None
        }
      case _: (Expr.ListLit | Expr.RecLit) => problem(e.pos,
        "a list or a record is written only in a test's call"); None
      case Expr.Apply("dec", List(a), _) if !scope.sigs.facts.contains("dec") =>
        expr(a, scope, Some(Sort.Int)).flatMap { x =>
          if x.sort == Sort.Int then Some(TExpr.ToDec(x))
          else { problem(a.pos, s"dec(...) takes an Int, given ${x.sort}"); None }
        }
      case Expr.Apply(n, as, pos) =>
        scope.sigs.facts.get(n) match
          case Some(FactSig(_, ps, Some(result), _, _)) => args(n, as, ps, pos, scope).map(TExpr.Fact(n, _, result))
          case Some(_) => problem(pos, s"$n is a relation: a condition, not a value"); None
          case None => scope.sigs.states.get(n) match
            case Some(sig) => args(n, as, sig.params, pos, scope).map(TExpr.State(n, _, sig.sort))
            case None => problem(pos, s"an unknown fact or state $n"); None
      case Expr.Add(a, b, pos) => arith(a, b, pos, scope, want)(TExpr.Add(_, _, _), "+")
      case Expr.Sub(a, b, pos) => arith(a, b, pos, scope, want)(TExpr.Sub(_, _, _), "-")
      case Expr.Mul(a, b, pos) =>
        val (x, lit) = (a, b) match
          case (_, _: (Expr.IntLit | Expr.DecLit)) => (a, b)
          case (_: (Expr.IntLit | Expr.DecLit), _) => (b, a)
          case _ =>
            problem(pos, s"a product by a literal only (the conditions stay linear): ${Printer.expr(e)}")
            return None
        expr(x, scope, want).flatMap { t =>
          if !numeric(t.sort) then { problem(pos, s"a product of a ${t.sort}"); None }
          else (lit, t.sort) match
            case (Expr.IntLit(v, _), Sort.Int) => Some(TExpr.Mul(t, Value.I(v), Sort.Int))
            case (Expr.IntLit(v, _), Sort.Dec) => Some(TExpr.Mul(t, Value.D(BigDecimal(v)), Sort.Dec))
            case (Expr.DecLit(v, _), Sort.Dec) => Some(TExpr.Mul(t, Value.D(v), Sort.Dec))
            case _ => problem(pos, "an Int times a decimal: dec(...) first"); None
        }

    private def arith(a: Expr, b: Expr, pos: Pos, scope: Scope, want: Option[Sort])(
      make: (TExpr, TExpr, Sort) => TExpr, op: String): Option[TExpr] =
      for
        x <- expr(a, scope, want)
        y <- expr(b, scope, want.orElse(Some(x.sort)))
        s <- join(x, y, pos, op)
        l <- fit(x, s, a.pos)
        r <- fit(y, s, b.pos)
      yield make(l, r, s)

    /** the sort two numbers meet in: the same, or `Dec` with an `Int` literal lifted to it */
    private def join(x: TExpr, y: TExpr, pos: Pos, op: String): Option[Sort] =
      val (a, b) = (x.sort, y.sort)
      val intLiteral = (e: TExpr) => e match
        case TExpr.Lit(Value.I(_)) => true
        case _ => false
      if !numeric(a) || !numeric(b) then { problem(pos, s"$op of $a and $b: numbers only"); None }
      else if a == b then Some(a)
      else if intLiteral(x) || intLiteral(y) then Some(Sort.Dec)
      else { problem(pos, s"$op of $a and $b: dec(...) to make an Int a Dec"); None }

    /** two sides of a comparison: the side that is a name of no variable takes the other's sort */
    private def sides(a: Expr, b: Expr, scope: Scope): Option[(TExpr, TExpr)] =
      val bare = (e: Expr) => e match
        case Expr.Var(n, _) => !scope.env.contains(n.takeWhile(_ != '.')) && !scope.args.contains(n.takeWhile(_ != '.'))
        case _ => false
      if bare(a) && !bare(b) then
        for y <- expr(b, scope, None); x <- expr(a, scope, Some(y.sort)) yield (x, y)
      else
        for x <- expr(a, scope, None); y <- expr(b, scope, Some(x.sort)) yield (x, y)

    private def cond(c: Cond, scope: Scope): Option[TCond] = c match
      case Cond.And(a, b) =>
        val (x, y) = (cond(a, scope), cond(b, scope))
        for l <- x; r <- y yield TCond.And(l, r)
      case Cond.Or(a, b) =>
        val (x, y) = (cond(a, scope), cond(b, scope))
        for l <- x; r <- y yield TCond.Or(l, r)
      case Cond.Not(a, _) => cond(a, scope).map(TCond.Not(_))
      case Cond.Flag(p, pos) => path(p, pos, scope).flatMap {
        case Named.Leaf(TExpr.Fact(n, List(base), Sort.Bool)) => Some(TCond.Holds(n, List(base)))
        case _ => problem(pos, s"$p is not a Bool: a condition needs a comparison"); None
      }
      case Cond.Has(p, pos) => path(p, pos, scope).map {
        case Named.Leaf(TExpr.Fact(n, List(base), _)) => TCond.Holds("has:" + n, List(base))
        case Named.Leaf(v) => TCond.Holds("has:" + p, List(v)) // a bound element: always there
        case Named.Lst(l) => TCond.Holds("has:" + l.name, List(l.base))
        case Named.Record(n, base, _) => TCond.Holds("has:" + n, List(base))
      }
      case Cond.Every(x, l, body, pos) => quantified(x, l, body, pos, scope)(TCond.Every(_, _, _))
      case Cond.Exists(x, l, body, pos) => quantified(x, l, body, pos, scope)(TCond.Exists(_, _, _))
      case Cond.Holds(n, as, pos) => scope.sigs.facts.get(n) match
        case Some(FactSig(_, ps, None, _, _)) => args(n, as, ps, pos, scope).map(TCond.Holds(n, _))
        case Some(_) => problem(pos, s"$n is a function fact: compare its value (`$n(...) = ...`)"); None
        case None =>
          if scope.sigs.states.contains(n) then problem(pos, s"$n is a state: compare its value")
          else problem(pos, s"an unknown fact $n")
          None
      case Cond.Text(a, op, b, pos) =>
        for
          x <- expr(a, scope, Some(Sort.Text))
          y <- expr(b, scope, Some(Sort.Text))
          r <- if x.sort == Sort.Text && y.sort == Sort.Text then Some(TCond.Text(x, op, y))
               else { problem(pos, s"${x.sort} ${op.word} ${y.sort}: texts only"); None }
        yield r
      case Cond.In(a, os, pos) =>
        expr(a, scope, None).flatMap { x =>
          val ys = os.map(o => expr(o, scope, Some(x.sort)).flatMap(fit(_, x.sort, o.pos)))
          val l = if x.sort == Sort.Int && ys.flatten.exists(_.sort == Sort.Dec) then fit(x, Sort.Dec, pos) else Some(x)
          Option.when(ys.forall(_.isDefined))(ys.flatten).flatMap(ys2 => l.map(TCond.In(_, ys2)))
        }
      case Cond.Compare(a, cmp, b, pos) =>
        sides(a, b, scope).flatMap { (x, y) =>
          val s =
            if x.sort == y.sort then Some(x.sort)
            else if numeric(x.sort) && numeric(y.sort) then Some(Sort.Dec)
            else { problem(pos, s"${x.sort} ${cmp.text} ${y.sort}: different sorts"); None }
          s.flatMap { s =>
            val ordered = cmp match
              case Cmp.Eq | Cmp.Ne => true
              case _ => numeric(s)
            if !ordered then { problem(pos, s"${cmp.text} on $s: an order of numbers only"); None }
            else if cmp == Cmp.Ne && s.isInstanceOf[Sort.Entity] then
              problem(pos, s"!= between ${s}s: not yet (two names are not known to be two things)")
              None
            else for l <- fit(x, s, a.pos); r <- fit(y, s, b.pos) yield TCond.Compare(l, cmp, r)
          }
        }

    private def quantified(x: String, l: String, body: Cond, pos: Pos, scope: Scope)(
      make: (String, TList, TCond) => TCond): Option[TCond] =
      if scope.env.contains(x) || scope.args.contains(x) then
        problem(pos, s"$x is taken: an element needs a name of its own")
        None
      else path(l, pos, scope).flatMap {
        case Named.Lst(list) => cond(body, scope.bind(x, list.elem)).map(make(x, list, _))
        case _ => problem(pos, s"$l is not a list"); None
      }

    private def test(t: Decl.Test, sigs: Sigs): Option[TTest] =
      // a tool the policy does not declare: called with its arguments unread — the open rules and the default decide
      val call = sigs.calls.get(t.tool)
      val noVars = Scope(Map.empty, Map.empty, sigs, Target.Tool(t.tool), List(t.tool))
      def constant(e: Expr, s: Sort): Option[Value] =
        expr(e, noVars, Some(s)).flatMap(fit(_, s, e.pos)).flatMap {
          case TExpr.Lit(v) => Some(v)
          case _ => problem(e.pos, s"a literal or a name, in a test: ${Printer.expr(e)}"); None
        }
      val givens = t.givens.flatMap {
        case Given.Holds(n, as, truth, pos) => sigs.facts.get(n) match
          case Some(FactSig(_, ps, None, _, _)) if ps.length == as.length =>
            val vs = as.zip(ps).map(constant(_, _))
            Option.when(vs.forall(_.isDefined))(TGiven(n, vs.flatten, Left(truth)))
          case Some(FactSig(_, ps, None, _, _)) => problem(pos, s"$n takes ${ps.length}, given ${as.length}"); None
          case Some(_) => problem(pos, s"$n is a function fact: give its value (`$n(...) = ...`)"); None
          case None => problem(pos, s"an unknown relation fact $n"); None
        case Given.Value(n, as, v, pos) =>
          val sig = sigs.facts.get(n).flatMap(f => f.result.map((f.params, _)))
            .orElse(sigs.states.get(n).map(s => (s.params, s.sort)))
          sig match
            case Some((ps, result)) if ps.length == as.length =>
              val vs = as.zip(ps).map(constant(_, _))
              val value = constant(v, result)
              Option.when(vs.forall(_.isDefined) && value.isDefined)(TGiven(n, vs.flatten, Right(value.get)))
            case Some((ps, _)) => problem(pos, s"$n takes ${ps.length}, given ${as.length}"); None
            case None => problem(pos, s"an unknown function fact or state $n"); None
      }
      val callerValue = Value.E(Types.callerType, t.caller)
      /** a test's written value as the call's data of a sort */
      def data(e: Expr, s: Sort): Option[Data] = (e, s) match
        case (Expr.ListLit(items, _), Sort.ListOf(el)) =>
          val ds = items.map(data(_, el))
          Option.when(ds.forall(_.isDefined))(Data.Lst(ds.flatten))
        case (Expr.RecLit(fs, rp), Sort.Rec(r)) =>
          fields(fs.map((n, v) => (n, v, rp)), sigs.records(r), s"$r has no field", rp).map(Data.Rec(_))
        case (_, Sort.ListOf(_) | Sort.Rec(_)) => problem(e.pos, s"expected a $s, found ${Printer.expr(e)}"); None
        case (Expr.Var("true", _), Sort.Bool) => Some(Data.Bit(true))
        case (Expr.Var("false", _), Sort.Bool) => Some(Data.Bit(false))
        case (_, Sort.Bool) => problem(e.pos, s"expected true or false, found ${Printer.expr(e)}"); None
        case _ => constant(e, s).map(Data.Leaf(_))
      def fields(supplied: List[(String, Expr, Pos)], of: List[Field], what: String, pos: Pos): Option[Map[String,
        Data]] =
        supplied.filterNot(g => of.exists(_.name == g._1)).foreach(g => problem(g._3, s"$what ${g._1}"))
        val written = supplied.map(g => g._1 -> g._2).toMap
        val out = of.map { f =>
          written.get(f.name) match
            case None =>
              if !f.optional then problem(pos, s"the call's argument ${f.name} is missing")
              (f.name, Some(None))
            case Some(v) => (f.name, data(v, f.sort).map(Some(_)))
        }
        Option.when(out.forall(_._2.isDefined))(out.flatMap((n, d) => d.get.map(n -> _)).toMap)
      val args = call.toList.flatMap(c =>
        fields(t.args.map(a => (a.name, a.value, a.pos)), c.params, s"${t.tool} has no argument",
          t.pos).toList.flatMap(_.toList)).toMap
      if !types(Types.callerType) then problem(t.pos, s"a test's caller is a ${Types.callerType}: declare the type")
      Some(TTest(t.name, givens, callerValue, t.tool, args, t.expect, t.because, t))
