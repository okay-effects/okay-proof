package okay.policy

/** A POLICY AS TEXT: canonical — parsed again it is the same policy (positions aside) */
object Printer:
  def apply(p: Policy): String =
    (s"policy ${p.name}" :: p.decls.map(decl)).mkString("", "\n\n", "\n")

  def decl(d: Decl): String = d match
    case Decl.Type(n, _) => s"type $n"
    case Decl.Fact(n, ps, result, source, _) =>
      s"fact $n(${params(ps)})" + result.fold("")(s => s": $s") + source.fold("")(s => s" from $s")
    case Decl.State(n, ps, s, window, init, _) =>
      s"state $n(${params(ps)}): $s" + window.fold("")(w => s" per ${w.word}") + s" = ${expr(init)}"
    case Decl.Call(tool, ps, _) => s"call $tool(${params(ps)})"
    case Decl.Rule(verdict, target, when, updates, because, _) =>
      s"${verdict.word} ${target.word}" +
        when.fold("")(c => s"\n  when ${cond(c)}") +
        (if updates.isEmpty then "" else updates.map(update).mkString("\n  then ", ", ", "")) +
        because.fold("")(b => s"\n  because ${quote(b)}")
    case Decl.Count(target, when, updates, _) =>
      s"count ${target.word}" + when.fold("")(c => s"\n  when ${cond(c)}") + updates.map(update).mkString("\n  then ", ", ", "")
    case Decl.Test(n, givens, caller, tool, args, expect, because, _) =>
      s"test ${quote(n)}\n  given ${givens.map(givenText).mkString(", ")}\n  when $caller calls $tool(" +
        args.map(a => s"${a.name}: ${expr(a.value)}").mkString(", ") + s")\n  expect ${expect.word}" +
        because.fold("")(b => s" ${quote(b)}")

  private def params(ps: List[Param]): String = ps.map(p => s"${p.name}: ${p.sort}").mkString(", ")

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

  private def tight(c: Cond): String = c match
    case _: Cond.Or => s"(${cond(c)})"
    case _ => cond(c)

  private def atomic(c: Cond): String = c match
    case _: Cond.Or | _: Cond.And => s"(${cond(c)})"
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

  private def right(e: Expr): String = e match
    case _: Expr.Add | _: Expr.Sub => s"(${expr(e)})"
    case _ => expr(e)

  private def factor(e: Expr): String = e match
    case _: Expr.Add | _: Expr.Sub => s"(${expr(e)})"
    case _ => expr(e)
