package okay.policy

/** A POLICY AS TEXT: canonical — parsed again it is the same policy (positions aside) */
object Printer:
  def apply(p: Policy): String =
    (s"policy ${p.name}" :: p.decls.map(decl)).mkString("", "\n\n", "\n")

  def apply(f: TestFile): String =
    (s"tests for ${f.policy}" :: f.tests.map(decl)).mkString("", "\n\n", "\n")

  def decl(d: Decl): String = d match
    case Decl.Type(n, _) => s"type $n"
    case Decl.Record(n, fs, _) => s"type $n = { ${params(fs)} }"
    case Decl.Fact(n, ps, result, source, _, fetch) =>
      s"fact $n(${params(ps)})" + result.fold("")(s => s": $s") + (fetch match
        case Some(f) =>
          val as = f.args.map((k, v) => s"$k: ${expr(v)}").mkString(", ")
          s" from mcp ${f.tool}($as) at ${quote(f.at)}"
        case None => source.fold("")(s => s" from $s"))
    case Decl.State(n, ps, s, window, init, _) =>
      s"state $n(${params(ps)}): $s" + window.fold("")(w => s" per ${w.word}") + s" = ${expr(init)}"
    case Decl.Call(tool, ps, _) => s"call ${toolName(tool)}(${params(ps)})"
    case Decl.Rule(verdict, target, when, updates, because, _, notifies) =>
      s"${verdict.word} ${targetWord(target)}" +
        when.fold("")(c => s"\n  when ${cond(c)}") +
        (if updates.isEmpty then "" else updates.map(update).mkString("\n  then ", ", ", "")) +
        because.fold("")(b => s"\n  because ${quote(b)}") +
        (if notifies.isEmpty then "" else notifies.mkString("\n  notify ", ", ", ""))
    case Decl.Default(verdict, _) => s"default ${verdict.word}"
    case Decl.Webhook(n, Hook.Url(u), _) => s"webhook $n = ${quote(u)}"
    case Decl.Webhook(n, Hook.Env(v), _) => s"webhook $n = env ${quote(v)}"
    case Decl.Notify(ns, on, target, when, _) =>
      s"notify ${ns.mkString(", ")} on ${on.words} ${targetWord(target)}" + when.fold("")(c => s"\n  when ${cond(c)}")
    case Decl.Count(target, when, updates, _) =>
      s"count ${targetWord(target)}" + when.fold("")(c => s"\n  when ${cond(c)}") +
        updates.map(update).mkString("\n  then ", ", ", "")
    case Decl.Test(n, givens, caller, tool, args, expect, because, _) =>
      s"test ${quote(n)}" + (if givens.isEmpty then "" else s"\n  given ${givens.map(givenText).mkString(", ")}") +
        s"\n  when $caller calls ${toolName(tool)}(" +
        args.map(a => s"${a.name}: ${expr(a.value)}").mkString(", ") + s")\n  expect ${expect.word}" +
        because.fold("")(b => s" ${quote(b)}")

  /** a tool's name as written: a text if it is no name (`"list-files"`) */
  def toolName(t: String): String =
    val plain = t.nonEmpty && (t.head.isLetter || t.head == '_') &&
      t.forall(c => c.isLetterOrDigit || c == '_' || c == '.')
    if plain then t
    else quote(t)

  private def targetWord(t: Target): String = t match
    case Target.Tool(n) => toolName(n)
    case other => other.word

  private def params(ps: List[Param]): String =
    ps.map(p => s"${p.name}${if p.optional then "?" else ""}: ${p.sort}").mkString(", ")

  private def update(u: Update): String =
    s"${u.state}(${u.key.map(expr).mkString(", ")}) ${u.change.text} ${expr(u.value)}"

  private def givenText(g: Given): String = g match
    case Given.Holds(n, as, truth, _) => (if truth then "" else "not ") + s"$n(${as.map(expr).mkString(", ")})"
    case Given.Value(n, as, v, _) => s"$n(${as.map(expr).mkString(", ")}) = ${expr(v)}"

  def quote(s: String): String =
    "\"" + s.flatMap {
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\n' => "\\n"
      case '\t' => "\\t"
      case c => c.toString
    } + "\""

  /** a condition: `or` and `and` in parentheses where they are inside a tighter one */
  def cond(c: Cond): String = c match
    case Cond.Or(a, b) => s"${cond(a)} or ${cond(b)}"
    case Cond.And(a, b) => s"${tight(a)} and ${tight(b)}"
    case Cond.Not(c, _) => s"not ${atomic(c)}"
    case Cond.Compare(a, cmp, b, _) => s"${expr(a)} ${cmp.text} ${expr(b)}"
    case Cond.In(a, os, _) => s"${expr(a)} in [${os.map(expr).mkString(", ")}]"
    case Cond.Holds(n, as, _) => s"$n(${as.map(expr).mkString(", ")})"
    case Cond.Text(a, op, b, _) => s"${expr(a)} ${op.word} ${expr(b)}"
    case Cond.Has(path, _) => s"has($path)"
    case Cond.Flag(path, _) => path
    case Cond.Every(x, l, body, _) => s"every $x in $l: ${atomic(body)}"
    case Cond.Exists(x, l, body, _) => s"some $x in $l: ${atomic(body)}"

  private def tight(c: Cond): String = c match
    case _: Cond.Or => s"(${cond(c)})"
    case _ => cond(c)

  private def atomic(c: Cond): String = c match
    case _: Cond.Or | _: Cond.And | _: Cond.Every | _: Cond.Exists => s"(${cond(c)})"
    case _ => cond(c)

  def expr(e: Expr): String = e match
    case Expr.IntLit(v, _) => v.toString
    case Expr.DecLit(v, _) => v.bigDecimal.toPlainString
    case Expr.TextLit(v, _) => quote(v)
    case Expr.Var(n, _) => n
    case Expr.Apply(n, as, _) => s"$n(${as.map(expr).mkString(", ")})"
    case Expr.Add(a, b, _) => s"${expr(a)} + ${right(b)}"
    case Expr.Sub(a, b, _) => s"${expr(a)} - ${right(b)}"
    case Expr.Mul(a, b, _) => s"${factor(a)} * ${factor(b)}"
    case Expr.ListLit(items, _) => items.map(expr).mkString("[", ", ", "]")
    case Expr.RecLit(fields, _) => fields.map((n, v) => s"$n: ${expr(v)}").mkString("{ ", ", ", " }")

  private def right(e: Expr): String = e match
    case _: Expr.Add | _: Expr.Sub => s"(${expr(e)})"
    case _ => expr(e)

  private def factor(e: Expr): String = e match
    case _: Expr.Add | _: Expr.Sub => s"(${expr(e)})"
    case _ => expr(e)
