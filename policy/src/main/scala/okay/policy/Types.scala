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

/** A CHECKED CONDITION */
enum TCond:
  case Compare(a: TExpr, cmp: Cmp, b: TExpr)
  case In(a: TExpr, options: List[TExpr])
  case Holds(name: String, args: List[TExpr])
  case Text(a: TExpr, op: TextOp, b: TExpr)
  case And(a: TCond, b: TCond)
  case Or(a: TCond, b: TCond)
  case Not(c: TCond)

final case class TUpdate(state: String, key: List[TExpr], change: Change, value: TExpr)

final case class FactSig(name: String, params: List[Sort], result: Option[Sort], source: Option[String])
final case class StateSig(name: String, params: List[Sort], sort: Sort, window: Option[Window], init: Value)
final case class CallSig(tool: String, params: List[(String, Sort)])

/** a rule checked: the tools it decides, its condition and updates over their common variables */
final case class TRule(index: Int, verdict: Verdict, tools: List[String], when: Option[TCond], updates: List[TUpdate],
                       because: Option[String], source: Decl.Rule)

/** a count checked: the tools whose calls it counts, its condition, its updates */
final case class TCount(tools: List[String], when: Option[TCond], updates: List[TUpdate], source: Decl.Count)

final case class TGiven(name: String, args: List[Value], value: Either[Boolean, Value])
final case class TTest(name: String, givens: List[TGiven], caller: Value, tool: String, args: Map[String, Value],
                       expect: Verdict, because: Option[String], source: Decl.Test)

/** A POLICY CHECKED: its signatures, and its rules and tests over them — what the evaluator runs */
final case class Checked(policy: Policy, types: Set[String], facts: Map[String, FactSig],
                         states: Map[String, StateSig], calls: Map[String, CallSig], rules: List[TRule],
                         counts: List[TCount]):
  /** the rules deciding `tool`, in the policy's order */
  lazy val rulesOf: Map[String, List[TRule]] = calls.keys.map(t => t -> rules.filter(_.tools.contains(t))).toMap
  /** the counts of `tool`'s calls */
  lazy val countsOf: Map[String, List[TCount]] = calls.keys.map(t => t -> counts.filter(_.tools.contains(t))).toMap

/** THE TYPE CHECKER: every problem of a policy, each with its place — or the policy checked */
object Types:
  /** the sort of `caller`: a policy that uses it declares `type User` */
  val callerType = "User"

  def check(p: Policy): Either[List[Problem], Checked] = Checking(p).run()

  /** a condition with its negations on atoms alone (`not (a and b)` is `not a or not b`): what a decision's proof
   * can take apart — the policy means the same */
  def nnf(c: TCond): TCond = c match
    case TCond.And(a, b) => TCond.And(nnf(a), nnf(b))
    case TCond.Or(a, b) => TCond.Or(nnf(a), nnf(b))
    case TCond.Not(TCond.Not(a)) => nnf(a)
    case TCond.Not(TCond.And(a, b)) => TCond.Or(nnf(TCond.Not(a)), nnf(TCond.Not(b)))
    case TCond.Not(TCond.Or(a, b)) => TCond.And(nnf(TCond.Not(a)), nnf(TCond.Not(b)))
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
    private def known(s: Sort, pos: Pos): Boolean = s match
      case Sort.Entity(n) if !types(n) => problem(pos, s"an unknown type $n"); false
      case _ => true

    def run(): Either[List[Problem], Checked] =
      duplicates(p.types.map(t => (t.name, t.pos)), "type")
      duplicates((p.facts.map(f => (f.name, f.pos)) ++ p.states.map(s => (s.name, s.pos))), "fact or state")
      duplicates(p.calls.map(c => (c.tool, c.pos)), "call")
      val facts = p.facts.map { f =>
        f.params.foreach(x => known(x.sort, x.pos))
        f.result.foreach(known(_, f.pos))
        duplicates(f.params.map(x => (x.name, x.pos)), "parameter")
        f.name -> FactSig(f.name, f.params.map(_.sort), f.result, f.source)
      }.toMap
      val states = p.states.flatMap { s =>
        s.params.foreach(x => known(x.sort, x.pos))
        known(s.sort, s.pos)
        if s.sort == Sort.Text || s.sort.isInstanceOf[Sort.Entity] then
          problem(s.pos, s"a state is a number: ${s.name} is ${s.sort}")
        literal(s.init, s.sort).map(v => s.name -> StateSig(s.name, s.params.map(_.sort), s.sort, s.window, v))
      }.toMap
      val calls = p.calls.map { c =>
        c.params.foreach(x => known(x.sort, x.pos))
        duplicates(c.params.map(x => (x.name, x.pos)), "argument")
        c.params.find(x => x.name == "caller" || x.name == "tool")
          .foreach(x => problem(x.pos, s"`${x.name}` is every call's own: not an argument"))
        c.tool -> CallSig(c.tool, c.params.map(x => (x.name, x.sort)))
      }.toMap
      val sigs = Sigs(facts, states, calls)
      val rules = p.rules.zipWithIndex.flatMap((r, i) => rule(r, i, sigs))
      val counts = p.counts.flatMap(count(_, sigs))
      if problems.isEmpty then Right(Checked(p, types, facts, states, calls, rules, counts))
      else Left(problems.toList.sortBy(q => (q.pos.line, q.pos.col)))

    def tests(c: Checked, f: TestFile): Either[List[Problem], List[TTest]] =
      if f.policy != c.policy.name then problem(f.pos, s"tests for ${f.policy}, not for ${c.policy.name}")
      val sigs = Sigs(c.facts, c.states, c.calls)
      duplicates(f.tests.map(t => (t.name, t.pos)), "test")
      val out = f.tests.flatMap(test(_, sigs))
      if problems.isEmpty then Right(out) else Left(problems.toList.sortBy(q => (q.pos.line, q.pos.col)))

    private def duplicates(names: List[(String, Pos)], what: String): Unit =
      names.groupBy(_._1).foreach((n, all) =>
        if all.size > 1 then all.sortBy((_, p) => (p.line, p.col)).tail.foreach((_, p) => problem(p, s"a $what $n again")))

    private final case class Sigs(facts: Map[String, FactSig], states: Map[String, StateSig],
                                  calls: Map[String, CallSig])

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
        case Target.Server(s) =>
          val ts = sigs.calls.keys.filter(_.startsWith(s + ".")).toList.sorted
          if ts.isEmpty then problem(pos, s"no tool of the server $s is declared")
          ts
        case Target.Any => sigs.calls.keys.toList.sorted
      val common = tools.map(t => sigs.calls.get(t).fold(Map.empty[String, Sort])(_.params.toMap))
      val args = common.headOption.fold(Map.empty[String, Sort])(first =>
        first.filter((n, s) => common.forall(_.get(n).contains(s))))
      Option.when(tools.nonEmpty && tools.forall(sigs.calls.contains))(
        Scope(args ++ Map("caller" -> Sort.Entity(callerType), "tool" -> Sort.Text), sigs, target, tools))

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

    private final case class Scope(env: Map[String, Sort], sigs: Sigs, target: Target, tools: List[String]):
      def missing(name: String, pos: Pos): Unit =
        val inSome = tools.filter(t => sigs.calls.get(t).exists(_.params.exists(_._1 == name)))
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
        problem(pos, s"$name takes ${sorts.length} argument${if sorts.length == 1 then "" else "s"}, given ${as.length}")
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
      case Expr.Var(n, pos) => scope.env.get(n) match
        case Some(s) => Some(TExpr.Var(n, s))
        case None => want match
          case Some(Sort.Entity(t)) => Some(TExpr.Lit(Value.E(t, n)))
          case _ => scope.missing(n, pos); None
      case Expr.Apply("dec", List(a), _) if !scope.sigs.facts.contains("dec") =>
        expr(a, scope, Some(Sort.Int)).flatMap { x =>
          if x.sort == Sort.Int then Some(TExpr.ToDec(x))
          else { problem(a.pos, s"dec(...) takes an Int, given ${x.sort}"); None }
        }
      case Expr.Apply(n, as, pos) =>
        scope.sigs.facts.get(n) match
          case Some(FactSig(_, ps, Some(result), _)) => args(n, as, ps, pos, scope).map(TExpr.Fact(n, _, result))
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
        case Expr.Var(n, _) => !scope.env.contains(n)
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
      case Cond.Holds(n, as, pos) => scope.sigs.facts.get(n) match
        case Some(FactSig(_, ps, None, _)) => args(n, as, ps, pos, scope).map(TCond.Holds(n, _))
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

    private def test(t: Decl.Test, sigs: Sigs): Option[TTest] =
      val call = sigs.calls.get(t.tool)
      if call.isEmpty then problem(t.pos, s"an unknown tool ${t.tool}")
      val noVars = Scope(Map.empty, sigs, Target.Tool(t.tool), List(t.tool))
      def constant(e: Expr, s: Sort): Option[Value] =
        expr(e, noVars, Some(s)).flatMap(fit(_, s, e.pos)).flatMap {
          case TExpr.Lit(v) => Some(v)
          case _ => problem(e.pos, s"a literal or a name, in a test: ${Printer.expr(e)}"); None
        }
      val givens = t.givens.flatMap {
        case Given.Holds(n, as, truth, pos) => sigs.facts.get(n) match
          case Some(FactSig(_, ps, None, _)) if ps.length == as.length =>
            val vs = as.zip(ps).map(constant(_, _))
            Option.when(vs.forall(_.isDefined))(TGiven(n, vs.flatten, Left(truth)))
          case Some(FactSig(_, ps, None, _)) => problem(pos, s"$n takes ${ps.length}, given ${as.length}"); None
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
      val args = call.toList.flatMap { c =>
        val written = t.args.map(a => a.name -> a).toMap
        t.args.filterNot(a => c.params.exists(_._1 == a.name))
          .foreach(a => problem(a.pos, s"${t.tool} has no argument ${a.name}"))
        c.params.flatMap { (n, s) =>
          written.get(n) match
            case None => problem(t.pos, s"the call's argument $n is missing"); None
            case Some(a) => constant(a.value, s).map(n -> _)
        }
      }.toMap
      if !types(Types.callerType) then problem(t.pos, s"a test's caller is a ${Types.callerType}: declare the type")
      Option.when(call.isDefined)(TTest(t.name, givens, callerValue, t.tool, args, t.expect, t.because, t))
