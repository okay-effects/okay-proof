package okay.policy

/** A CALL to decide: its tool, who calls, its arguments by name */
final case class Call(tool: String, caller: Value, args: Map[String, Value]):
  /** the variables of a rule: `caller`, `tool`, the arguments */
  def env: Map[String, Value] = args + ("caller" -> caller) + ("tool" -> Value.T(tool))

/** what a decision reads: the facts answered, the states' values */
final case class Known(facts: Map[FactRef, Answer], states: Map[FactRef, Value])

/**
 * THE EVALUATOR, untrusted: a condition's truth under a call and what is known — `None` where a fact it needs is
 * unknown. It only chooses; the kernel proves (`Prove`).
 */
object Eval:
  def plus(a: Value, b: Value): Value = (a, b) match
    case (Value.I(x), Value.I(y)) => Value.I(x + y)
    case (Value.D(x), Value.D(y)) => Value.D(x + y)
    case _ => throw IllegalArgumentException(s"$a + $b")

  def minus(a: Value, b: Value): Value = (a, b) match
    case (Value.I(x), Value.I(y)) => Value.I(x - y)
    case (Value.D(x), Value.D(y)) => Value.D(x - y)
    case _ => throw IllegalArgumentException(s"$a - $b")

  /** an expression's arguments, as values: a fact's are variables or literals */
  def ref(name: String, args: List[TExpr], env: Map[String, Value]): FactRef =
    FactRef(name, args.map {
      case TExpr.Lit(v) => v
      case TExpr.Var(n, _) => env(n)
      case TExpr.ToDec(TExpr.Var(n, _)) => env(n) match
        case Value.I(i) => Value.D(BigDecimal(i))
        case v => v
      case other => throw IllegalStateException(s"a fact's argument not checked: $other")
    })

  /** every fact and state an expression or condition reads, under `env` */
  def refs(e: TExpr, env: Map[String, Value]): List[(Boolean, FactRef)] = e match
    case TExpr.Fact(n, as, _) => List(false -> ref(n, as, env))
    case TExpr.State(n, as, _) => List(true -> ref(n, as, env))
    case TExpr.Add(a, b, _) => refs(a, env) ++ refs(b, env)
    case TExpr.Sub(a, b, _) => refs(a, env) ++ refs(b, env)
    case TExpr.Mul(a, _, _) => refs(a, env)
    case TExpr.ToDec(a) => refs(a, env)
    case _ => Nil

  def refs(c: TCond, env: Map[String, Value]): List[(Boolean, FactRef)] = c match
    case TCond.Compare(a, _, b) => refs(a, env) ++ refs(b, env)
    case TCond.In(a, os) => refs(a, env) ++ os.flatMap(refs(_, env))
    case TCond.Holds(n, as) => List(false -> ref(n, as, env))
    case TCond.Text(a, _, b) => refs(a, env) ++ refs(b, env)
    case TCond.And(a, b) => refs(a, env) ++ refs(b, env)
    case TCond.Or(a, b) => refs(a, env) ++ refs(b, env)
    case TCond.Not(a) => refs(a, env)

  def value(e: TExpr, env: Map[String, Value], known: Known): Option[Value] = e match
    case TExpr.Lit(v) => Some(v)
    case TExpr.Var(n, _) => env.get(n)
    case TExpr.Fact(n, as, _) => known.facts.get(ref(n, as, env)) match
      case Some(Answer.Is(v)) => Some(v)
      case _ => None
    case TExpr.State(n, as, _) => known.states.get(ref(n, as, env))
    case TExpr.Add(a, b, _) => for x <- value(a, env, known); y <- value(b, env, known) yield plus(x, y)
    case TExpr.Sub(a, b, _) => for x <- value(a, env, known); y <- value(b, env, known) yield minus(x, y)
    case TExpr.Mul(a, by, _) => value(a, env, known).map(x => (x, by) match
      case (Value.I(p), Value.I(q)) => Value.I(p * q)
      case (Value.D(p), Value.D(q)) => Value.D(p * q)
      case _ => throw IllegalArgumentException(s"$x * $by"))
    case TExpr.ToDec(a) => value(a, env, known).map {
      case Value.I(i) => Value.D(BigDecimal(i))
      case v => v
    }

  private def compare(a: Value, b: Value): Int = (a, b) match
    case (Value.I(x), Value.I(y)) => x.compare(y)
    case (Value.D(x), Value.D(y)) => x.compare(y)
    case _ => throw IllegalArgumentException(s"$a compared with $b")

  private def same(a: Value, b: Value): Boolean = (a, b) match
    case (Value.D(x), Value.D(y)) => x.compare(y) == 0
    case _ => a == b

  /** the condition's truth; `None`: a fact it needs is unknown */
  def holds(c: TCond, env: Map[String, Value], known: Known): Option[Boolean] = c match
    case TCond.Compare(a, cmp, b) =>
      for x <- value(a, env, known); y <- value(b, env, known) yield cmp match
        case Cmp.Eq => same(x, y)
        case Cmp.Ne => !same(x, y)
        case Cmp.Lt => compare(x, y) < 0
        case Cmp.Le => compare(x, y) <= 0
        case Cmp.Gt => compare(x, y) > 0
        case Cmp.Ge => compare(x, y) >= 0
    case TCond.In(a, os) =>
      value(a, env, known).flatMap { x =>
        val vs = os.map(value(_, env, known))
        if vs.exists(_.exists(same(x, _))) then Some(true) else if vs.forall(_.isDefined) then Some(false) else None
      }
    case TCond.Holds(n, as) => known.facts.get(ref(n, as, env)) match
      case Some(Answer.Holds(t)) => Some(t)
      case _ => None
    case TCond.Text(a, op, b) =>
      for case Value.T(x) <- value(a, env, known); case Value.T(y) <- value(b, env, known) yield op match
        case TextOp.Starts => x.startsWith(y)
        case TextOp.Ends => x.endsWith(y)
        case TextOp.Contains => x.contains(y)
    case TCond.And(a, b) => (holds(a, env, known), holds(b, env, known)) match
      case (Some(false), _) | (_, Some(false)) => Some(false)
      case (Some(true), Some(true)) => Some(true)
      case _ => None
    case TCond.Or(a, b) => (holds(a, env, known), holds(b, env, known)) match
      case (Some(true), _) | (_, Some(true)) => Some(true)
      case (Some(false), Some(false)) => Some(false)
      case _ => None
    case TCond.Not(a) => holds(a, env, known).map(!_)

  /** why a condition does not hold: the parts that fail, with the values read */
  def why(c: TCond, env: Map[String, Value], known: Known): List[String] = c match
    case TCond.And(a, b) => why(a, env, known) ++ why(b, env, known)
    case TCond.Or(a, b) =>
      if holds(c, env, known).contains(true) then Nil else List((why(a, env, known) ++ why(b, env, known)).mkString(
        "neither ", " nor ", ""))
    case _ => holds(c, env, known) match
      case Some(true) => Nil
      case Some(false) => List(s"${show(c, env, known)} is false")
      case None => List(s"unknown: ${refs(c, env).map(_._2).filterNot(r =>
        known.facts.contains(r) || known.states.contains(r)).mkString(", ")}")

  /** a condition as written, its variables and facts with their values */
  def show(c: TCond, env: Map[String, Value], known: Known): String = c match
    case TCond.Compare(a, cmp, b) => s"${show(a, env, known)} ${cmp.text} ${show(b, env, known)}"
    case TCond.In(a, os) => s"${show(a, env, known)} in [${os.map(show(_, env, known)).mkString(", ")}]"
    case TCond.Holds(n, as) => ref(n, as, env).toString
    case TCond.Text(a, op, b) => s"${show(a, env, known)} ${op.word} ${show(b, env, known)}"
    case TCond.And(a, b) => s"${show(a, env, known)} and ${show(b, env, known)}"
    case TCond.Or(a, b) => s"(${show(a, env, known)} or ${show(b, env, known)})"
    case TCond.Not(a) => s"not ${show(a, env, known)}"

  def show(e: TExpr, env: Map[String, Value], known: Known): String = e match
    case TExpr.Lit(v) => v.toString
    case TExpr.Var(n, _) => env.get(n).fold(n)(v => s"$n (${v})")
    case TExpr.Fact(n, as, _) => val r = ref(n, as, env); s"$r (${value(e, env, known).fold("unknown")(_.toString)})"
    case TExpr.State(n, as, _) => val r = ref(n, as, env); s"$r (${value(e, env, known).fold("unknown")(_.toString)})"
    case TExpr.Add(a, b, _) => s"${show(a, env, known)} + ${show(b, env, known)}"
    case TExpr.Sub(a, b, _) => s"${show(a, env, known)} - ${show(b, env, known)}"
    case TExpr.Mul(a, by, _) => s"${show(a, env, known)} * $by"
    case TExpr.ToDec(a) => s"dec(${show(a, env, known)})"
