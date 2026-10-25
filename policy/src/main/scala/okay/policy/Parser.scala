package okay.policy

import scala.collection.mutable.ArrayBuffer

/** a token of the text, with its place */
private enum Tok:
  case Name(text: String, pos: Pos)
  case IntNum(value: BigInt, pos: Pos)
  case DecNum(value: BigDecimal, pos: Pos)
  case Str(value: String, pos: Pos)
  case Sym(text: String, pos: Pos)
  case End(pos: Pos)

  def pos: Pos

  def show: String = this match
    case Name(t, _) => s"'$t'"
    case IntNum(v, _) => v.toString
    case DecNum(v, _) => v.toString
    case Str(v, _) => s"\"$v\""
    case Sym(t, _) => s"'$t'"
    case End(_) => "the end"

/** the text in tokens: names (a tool's with dots: `stripe.create_payment`), numbers, texts, symbols; `--` comments */
private object Lexer:
  private val symbols = List("!=", "<=", ">=", "+=", "-=", ".*", "(", ")", "[", "]", "{", "}", ",", ":", "=", "<",
    ">", "+", "-", "*", "?")

  def apply(text: String): Either[Problem, Vector[Tok]] =
    val out = ArrayBuffer.empty[Tok]
    var i = 0
    var line = 1
    var lineStart = 0
    def pos = Pos(line, i - lineStart + 1)
    var problem: Option[Problem] = None
    while problem.isEmpty && i < text.length do
      val c = text(i)
      if c == '\n' then
        i += 1
        line += 1
        lineStart = i
      else if c.isWhitespace then i += 1
      else if text.startsWith("--", i) then
        while i < text.length && text(i) != '\n' do i += 1
      else if c.isLetter || c == '_' then
        val at = pos
        val start = i
        while i < text.length && (text(i).isLetterOrDigit || text(i) == '_' ||
            (text(i) == '.' && i + 1 < text.length && (text(i + 1).isLetter || text(i + 1) == '_'))) do i += 1
        out += Tok.Name(text.substring(start, i), at)
      else if c.isDigit then
        val at = pos
        val start = i
        while i < text.length && text(i).isDigit do i += 1
        if i + 1 < text.length && text(i) == '.' && text(i + 1).isDigit then
          i += 1
          while i < text.length && text(i).isDigit do i += 1
          out += Tok.DecNum(BigDecimal(text.substring(start, i)), at)
        else out += Tok.IntNum(BigInt(text.substring(start, i)), at)
      else if c == '"' then
        val at = pos
        val b = StringBuilder()
        i += 1
        var closed = false
        while problem.isEmpty && !closed && i < text.length do
          text(i) match
            case '"' =>
              closed = true
              i += 1
            case '\\' if i + 1 < text.length =>
              text(i + 1) match
                case 'n' => b += '\n'
                case 't' => b += '\t'
                case '"' => b += '"'
                case '\\' => b += '\\'
                case other => problem = Some(Problem(pos, s"an unknown escape \\$other"))
              i += 2
            case '\n' => problem = Some(Problem(at, "a text not closed on its line"))
            case ch =>
              b += ch
              i += 1
        if problem.isEmpty && !closed then problem = Some(Problem(at, "a text not closed"))
        out += Tok.Str(b.toString, at)
      else symbols.find(text.startsWith(_, i)) match
        case Some(s) =>
          out += Tok.Sym(s, pos)
          i += s.length
        case None => problem = Some(Problem(pos, s"an unexpected character '$c'"))
    problem.toLeft(out.toVector :+ Tok.End(pos))

/** THE PARSER: the text to a `Policy`, or the first problem, with its place. Recursive descent; newlines mean nothing
 * — a declaration begins with its keyword */
object Parser:
  private val declWords = Set("type", "fact", "state", "call", "allow", "ask", "deny", "count", "test")
  /** the words no name may be; the others (`from`, `per`, `given`, `calls`, `expect`) are keywords only where they
   * stand, so a state may be called `calls` */
  private val keywords = declWords ++ Set("policy", "when", "then", "because", "and", "or", "not", "in")

  def parse(text: String): Either[Problem, Policy] =
    Lexer(text).flatMap(toks => Parsing(toks).policy())

  /** a file of tests: `tests for <policy>`, then `test` blocks */
  def parseTests(text: String): Either[Problem, TestFile] =
    Lexer(text).flatMap(toks => Parsing(toks).tests())

  private final class Fail(val problem: Problem) extends RuntimeException(null, null, false, false)

  private final class Parsing(toks: Vector[Tok]):
    private var at = 0
    private def peek: Tok = toks(at)
    private def peekAt(n: Int): Tok = toks(math.min(at + n, toks.length - 1))
    private def next(): Tok =
      val t = toks(at)
      if at < toks.length - 1 then at += 1
      t
    private def fail(pos: Pos, message: String): Nothing = throw Fail(Problem(pos, message))
    private def expected(what: String): Nothing = fail(peek.pos, s"expected $what, found ${peek.show}")

    private def isWord(w: String): Boolean = peek match
      case Tok.Name(`w`, _) => true
      case _ => false
    private def isSym(s: String): Boolean = peek match
      case Tok.Sym(`s`, _) => true
      case _ => false
    private def word(w: String): Pos =
      if isWord(w) then next().pos else expected(s"'$w'")
    private def sym(s: String): Pos =
      if isSym(s) then next().pos else expected(s"'$s'")
    private def acceptWord(w: String): Boolean = isWord(w) && { next(); true }
    private def acceptSym(s: String): Boolean = isSym(s) && { next(); true }

    /** a name that is not a keyword */
    private def name(what: String): (String, Pos) = peek match
      case Tok.Name(t, p) if !keywords(t) =>
        next()
        (t, p)
      case _ => expected(what)

    /** a tool's name: a name (`stripe.refund`), or a text for one no name can be (`"list-files"`) */
    private def tool(what: String): String = peek match
      case Tok.Str(v, _) if v.nonEmpty =>
        next()
        v
      case _ => name(what)._1

    private def text(what: String): String = peek match
      case Tok.Str(v, _) =>
        next()
        v
      case _ => expected(what)

    def policy(): Either[Problem, Policy] =
      try
        word("policy")
        val (n, _) = name("the policy's name")
        val decls = ArrayBuffer.empty[Decl]
        while !peek.isInstanceOf[Tok.End] do decls += decl()
        Right(Policy(n, decls.toList))
      catch case f: Fail => Left(f.problem)

    def tests(): Either[Problem, TestFile] =
      try
        val p = word("tests")
        word("for")
        val (n, _) = name("the policy's name")
        val out = ArrayBuffer.empty[Decl.Test]
        while !peek.isInstanceOf[Tok.End] do
          peek match
            case Tok.Name("test", tp) => out += test(tp)
            case _ => expected("a test")
        Right(TestFile(n, out.toList, p))
      catch case f: Fail => Left(f.problem)

    private def decl(): Decl = peek match
      case Tok.Name("type", p) =>
        next()
        val (n, np) = name("a type's name")
        if !n.head.isUpper then fail(np, s"a type's name starts with a capital: $n")
        if acceptSym("=") then
          sym("{")
          val fields = ArrayBuffer(param())
          while acceptSym(",") do fields += param()
          sym("}")
          Decl.Record(n, fields.toList, p)
        else Decl.Type(n, p)
      case Tok.Name("fact", p) =>
        next()
        val (n, _) = name("a fact's name")
        val ps = params()
        val result = if acceptSym(":") then Some(sort()) else None
        if acceptWord("from") then
          if isWord("mcp") && peekAt(1).isInstanceOf[Tok.Name] then
            val fp = next().pos
            val (tool, _) = name("an MCP tool: server.tool")
            sym("(")
            val as = ArrayBuffer.empty[(String, Expr)]
            if !isSym(")") then
              as += field()
              while acceptSym(",") do as += field()
            sym(")")
            word("at")
            val at = text("a path in the tool's result, in quotes")
            Decl.Fact(n, ps, result, Some("mcp:" + tool), p, Some(Fetch(tool, as.toList, at, fp)))
          else Decl.Fact(n, ps, result, Some(name("a source's name")._1), p)
        else Decl.Fact(n, ps, result, None, p)
      case Tok.Name("state", p) =>
        next()
        val (n, _) = name("a state's name")
        val ps = params()
        sym(":")
        val s = sort()
        val window = if acceptWord("per") then Some(this.window()) else None
        sym("=")
        Decl.State(n, ps, s, window, expr(), p)
      case Tok.Name("call", p) =>
        next()
        val tool = this.tool("a tool's name")
        Decl.Call(tool, params(), p)
      case Tok.Name("allow" | "ask" | "deny", p) => rule(p)
      case Tok.Name("count", p) =>
        next()
        val target = this.target()
        val when = if acceptWord("when") then Some(cond()) else None
        word("then")
        val updates = ArrayBuffer(update())
        while acceptSym(",") do updates += update()
        Decl.Count(target, when, updates.toList, p)
      case Tok.Name("test", p) => fail(p, "a test goes in the policy's file of tests (`tests for <policy>`), not in it")
      case _ => expected("a declaration: type, fact, state, call, allow, ask, deny or count")

    private def window(): Window = peek match
      case Tok.Name("minute", _) => next(); Window.Minute
      case Tok.Name("hour", _) => next(); Window.Hour
      case Tok.Name("day", _) => next(); Window.Day
      case _ => expected("minute, hour or day")

    private def params(): List[Param] =
      sym("(")
      val out = ArrayBuffer.empty[Param]
      if !isSym(")") then
        out += param()
        while acceptSym(",") do out += param()
      sym(")")
      out.toList

    private def param(): Param =
      val (n, p) = name("a parameter's name")
      val optional = acceptSym("?")
      sym(":")
      Param(n, sort(), p, optional)

    private def sort(): Sort = peek match
      case Tok.Name("Int", _) => next(); Sort.Int
      case Tok.Name("Dec", _) => next(); Sort.Dec
      case Tok.Name("Text", _) => next(); Sort.Text
      case Tok.Name("List", _) =>
        next()
        sym("[")
        val e = sort()
        sym("]")
        Sort.ListOf(e)
      case Tok.Name(t, _) if t.head.isUpper && !keywords(t) => next(); Sort.Entity(t)
      case _ => expected("a sort: Int, Dec, Text or a type")

    private def rule(p: Pos): Decl.Rule =
      val verdict = next() match
        case Tok.Name("allow", _) => Verdict.Allow
        case Tok.Name("ask", _) => Verdict.Ask
        case _ => Verdict.Deny
      val target = this.target()
      val when = if acceptWord("when") then Some(cond()) else None
      val updates = ArrayBuffer.empty[Update]
      if acceptWord("then") then
        updates += update()
        while acceptSym(",") do updates += update()
      val because = if acceptWord("because") then Some(text("a reason, in quotes")) else None
      Decl.Rule(verdict, target, when, updates.toList, because, p)

    private def target(): Target =
      if acceptSym("*") then Target.Any
      else
        peek match
          case Tok.Str(_, _) => Target.Tool(tool("a tool"))
          case _ =>
            val (n, _) = name("a tool, a server's `name.*`, or `*`")
            if acceptSym(".*") then Target.Server(n) else Target.Tool(n)

    private def update(): Update =
      val (n, p) = name("a state to change")
      val key = args()
      val change =
        if acceptSym("+=") then Change.Add
        else if acceptSym("-=") then Change.Sub
        else if acceptSym("=") then Change.Set
        else expected("'=', '+=' or '-='")
      Update(n, key, change, expr(), p)

    private def test(p: Pos): Decl.Test =
      next()
      val n = text("the test's name, in quotes")
      word("given")
      val givens = ArrayBuffer(fact())
      while acceptSym(",") do givens += fact()
      word("when")
      val (caller, _) = name("who calls")
      word("calls")
      val tool = this.tool("the tool called")
      sym("(")
      val as = ArrayBuffer.empty[Arg]
      if !isSym(")") then
        as += arg()
        while acceptSym(",") do as += arg()
      sym(")")
      word("expect")
      val verdict = peek match
        case Tok.Name("allow", _) => next(); Verdict.Allow
        case Tok.Name("ask", _) => next(); Verdict.Ask
        case Tok.Name("deny", _) => next(); Verdict.Deny
        case _ => expected("allow, ask or deny")
      val because = peek match
        case Tok.Str(v, _) => next(); Some(v)
        case _ => None
      Decl.Test(n, givens.toList, caller, tool, as.toList, verdict, because, p)

    private def fact(): Given =
      if acceptWord("not") then
        val (n, p) = name("a relation fact")
        Given.Holds(n, args(), false, p)
      else
        val (n, p) = name("a fact or a state")
        val as = args()
        if acceptSym("=") then Given.Value(n, as, expr(), p) else Given.Holds(n, as, true, p)

    private def arg(): Arg =
      val (n, p) = name("an argument's name")
      sym(":")
      Arg(n, expr(), p)

    private def args(): List[Expr] =
      sym("(")
      val out = ArrayBuffer.empty[Expr]
      if !isSym(")") then
        out += expr()
        while acceptSym(",") do out += expr()
      sym(")")
      out.toList

    // CONDITIONS: or < and < not < an atom

    private def cond(): Cond =
      var c = conj()
      while acceptWord("or") do c = Cond.Or(c, conj())
      c

    private def conj(): Cond =
      var c = negation()
      while acceptWord("and") do c = Cond.And(c, negation())
      c

    private def negation(): Cond =
      peek match
        case Tok.Name("not", p) =>
          next()
          Cond.Not(negation(), p)
        case Tok.Name("has", p) if peekAt(1) == Tok.Sym("(", peekAt(1).pos) =>
          next()
          sym("(")
          val (path, _) = name("an argument or a field")
          sym(")")
          Cond.Has(path, p)
        case Tok.Name(q @ ("every" | "some"), p) if peekAt(2) == Tok.Name("in", peekAt(2).pos) =>
          next()
          val (x, _) = name("an element's name")
          word("in")
          val (list, _) = name("a list")
          sym(":")
          val body = negation()
          if q == "every" then Cond.Every(x, list, body, p) else Cond.Exists(x, list, body, p)
        case Tok.Sym("(", _) =>
          // a condition in parentheses, or an expression in them that a comparison follows: tried as the first
          val start = at
          try
            next()
            val c = cond()
            sym(")")
            if isComparison then
              at = start
              atom()
            else c
          catch case _: Fail =>
            at = start
            atom()
        case _ => atom()

    private def isComparison: Boolean = peek match
      case Tok.Sym("=" | "!=" | "<" | "<=" | ">" | ">=" | "+" | "-" | "*", _) => true
      case Tok.Name("in" | "starts" | "ends" | "contains", _) => true
      case _ => false

    private def atom(): Cond =
      val a = expr()
      peek match
        case Tok.Sym(s @ ("=" | "!=" | "<" | "<=" | ">" | ">="), p) =>
          next()
          val cmp = s match
            case "=" => Cmp.Eq
            case "!=" => Cmp.Ne
            case "<" => Cmp.Lt
            case "<=" => Cmp.Le
            case ">" => Cmp.Gt
            case _ => Cmp.Ge
          Cond.Compare(a, cmp, expr(), p)
        case Tok.Name(w @ ("starts" | "ends" | "contains"), p) =>
          next()
          val op = w match
            case "starts" => TextOp.Starts
            case "ends" => TextOp.Ends
            case _ => TextOp.Contains
          Cond.Text(a, op, expr(), p)
        case Tok.Name("in", p) =>
          next()
          sym("[")
          val options = ArrayBuffer(expr())
          while acceptSym(",") do options += expr()
          sym("]")
          Cond.In(a, options.toList, p)
        case _ => a match
          case Expr.Apply(n, as, p) => Cond.Holds(n, as, p)
          case _ => expected("a comparison (=, !=, <, <=, >, >=), 'in', or a text test (starts, ends, contains)")

    // EXPRESSIONS: + and - < * < an atom

    private def expr(): Expr =
      var e = term()
      var going = true
      while going do
        peek match
          case Tok.Sym("+", p) =>
            next()
            e = Expr.Add(e, term(), p)
          case Tok.Sym("-", p) =>
            next()
            e = Expr.Sub(e, term(), p)
          case _ => going = false
      e

    private def term(): Expr =
      var e = factor()
      while isSym("*") do
        val p = next().pos
        e = Expr.Mul(e, factor(), p)
      e

    private def factor(): Expr = peek match
      case Tok.IntNum(v, p) => next(); Expr.IntLit(v, p)
      case Tok.DecNum(v, p) => next(); Expr.DecLit(v, p)
      case Tok.Str(v, p) => next(); Expr.TextLit(v, p)
      case Tok.Sym("-", p) =>
        next()
        peek match
          case Tok.IntNum(v, _) => next(); Expr.IntLit(-v, p)
          case Tok.DecNum(v, _) => next(); Expr.DecLit(-v, p)
          case _ => expected("a number after '-'")
      case Tok.Sym("(", _) =>
        next()
        val e = expr()
        sym(")")
        e
      case Tok.Name(n, p) if !keywords(n) || (n == "count" && peekAt(1).isInstanceOf[Tok.Sym]) =>
        next()
        if isSym("(") then Expr.Apply(n, args(), p) else Expr.Var(n, p)
      case Tok.Sym("[", p) =>
        next()
        val items = ArrayBuffer.empty[Expr]
        if !isSym("]") then
          items += expr()
          while acceptSym(",") do items += expr()
        sym("]")
        Expr.ListLit(items.toList, p)
      case Tok.Sym("{", p) =>
        next()
        val fields = ArrayBuffer.empty[(String, Expr)]
        if !isSym("}") then
          fields += field()
          while acceptSym(",") do fields += field()
        sym("}")
        Expr.RecLit(fields.toList, p)
      case _ => expected("a value: a number, a text, a name, a fact")

    private def field(): (String, Expr) =
      val (n, _) = name("a field's name")
      sym(":")
      (n, expr())
