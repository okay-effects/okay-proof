package okay.policy

/** a place in the policy's text: line and column, from 1 */
final case class Pos(line: Int, col: Int):
  override def toString: String = s"$line:$col"

/** what went wrong, and where */
final case class Problem(pos: Pos, message: String):
  override def toString: String = s"$pos: $message"

/** A SORT: the numbers, text, and the entity types a policy declares */
enum Sort:
  case Int, Dec, Text
  case Entity(name: String)
  /** a record type's: `type Item = { sku: Text, qty: Int }` */
  case Rec(name: String)
  case ListOf(elem: Sort)

  override def toString: String = this match
    case Entity(n) => n
    case Rec(n) => n
    case ListOf(e) => s"List[$e]"
    case s => s.productPrefix

enum Cmp:
  case Eq, Ne, Lt, Le, Gt, Ge

  def text: String = this match
    case Eq => "="
    case Ne => "!="
    case Lt => "<"
    case Le => "<="
    case Gt => ">"
    case Ge => ">="

/** an expression: a literal, a variable (`caller`, an argument), a fact or a state applied, a sum, a product by a
 * literal */
enum Expr:
  case IntLit(value: BigInt, pos: Pos)
  case DecLit(value: BigDecimal, pos: Pos)
  case TextLit(value: String, pos: Pos)
  case Var(name: String, pos: Pos)
  case Apply(name: String, args: List[Expr], pos: Pos)
  case Add(a: Expr, b: Expr, pos: Pos)
  case Sub(a: Expr, b: Expr, pos: Pos)
  case Mul(a: Expr, by: Expr, pos: Pos)
  /** in a test's call: a list, a record */
  case ListLit(items: List[Expr], pos: Pos)
  case RecLit(fields: List[(String, Expr)], pos: Pos)

  def pos: Pos

/** a condition */
enum Cond:
  case Compare(a: Expr, cmp: Cmp, b: Expr, pos: Pos)
  case In(a: Expr, options: List[Expr], pos: Pos)
  /** a relation fact */
  case Holds(name: String, args: List[Expr], pos: Pos)
  /** a text test: `path starts "/ws/"` */
  case Text(a: Expr, op: TextOp, b: Expr, pos: Pos)
  case And(a: Cond, b: Cond)
  case Or(a: Cond, b: Cond)
  case Not(c: Cond, pos: Pos)
  /** an optional argument or field given: `has(coupon)` */
  case Has(path: String, pos: Pos)
  /** each element of a list, or one of them: `every i in items: (...)` */
  case Every(name: String, list: String, body: Cond, pos: Pos)
  case Exists(name: String, list: String, body: Cond, pos: Pos)

/** how a text is tested against another */
enum TextOp:
  case Starts, Ends, Contains

  def word: String = productPrefix.toLowerCase

enum Verdict:
  case Allow, Ask, Deny

  def word: String = productPrefix.toLowerCase

/** what a rule decides: one tool, every tool of a server, or every call */
enum Target:
  case Tool(name: String)
  case Server(name: String)
  case Any

  def word: String = this match
    case Tool(n) => n
    case Server(s) => s + ".*"
    case Any => "*"

enum Change:
  case Set, Add, Sub

  def text: String = this match
    case Set => "="
    case Add => "+="
    case Sub => "-="

final case class Update(state: String, key: List[Expr], change: Change, value: Expr, pos: Pos)

/** a fact fetched by a tool of an MCP server: `from mcp stripe.retrieve_balance(account: account) at "available.0"` —
 * its arguments of the fact's parameters, its value at a path in the tool's result */
final case class Fetch(tool: String, args: List[(String, Expr)], at: String, pos: Pos)

final case class Param(name: String, sort: Sort, pos: Pos, optional: Boolean = false)

enum Window:
  case Minute, Hour, Day

  def word: String = productPrefix.toLowerCase

  def millis: Long = this match
    case Minute => 60_000L
    case Hour => 3_600_000L
    case Day => 86_400_000L

/** a `given` of a test: a relation fact, true (`owns(ann, acc1)`) or false (`not owns(ann, acc2)`), or a function
 * fact's or a state's value (`spent(ann) = 100.00`) */
enum Given:
  case Holds(name: String, args: List[Expr], truth: Boolean, pos: Pos)
  case Value(name: String, args: List[Expr], value: Expr, pos: Pos)

final case class Arg(name: String, value: Expr, pos: Pos)

enum Decl:
  case Type(name: String, pos: Pos)
  case Record(name: String, fields: List[Param], pos: Pos)
  case Fact(name: String, params: List[Param], result: Option[Sort], source: Option[String], pos: Pos,
            fetch: Option[Fetch] = None)
  case State(name: String, params: List[Param], sort: Sort, window: Option[Window], init: Expr, pos: Pos)
  case Call(tool: String, params: List[Param], pos: Pos)
  case Rule(verdict: Verdict, target: Target, when: Option[Cond], updates: List[Update], because: Option[String],
            pos: Pos)
  /** what is counted when a call goes ahead (allowed, or asked and approved): it decides nothing */
  case Count(target: Target, when: Option[Cond], updates: List[Update], pos: Pos)
  case Test(name: String, givens: List[Given], caller: String, tool: String, args: List[Arg], expect: Verdict,
            because: Option[String], pos: Pos)

  def pos: Pos

/** A POLICY, as written */
final case class Policy(name: String, decls: List[Decl]):
  def types: List[Decl.Type] = decls.collect { case d: Decl.Type => d }
  def records: List[Decl.Record] = decls.collect { case d: Decl.Record => d }
  def facts: List[Decl.Fact] = decls.collect { case d: Decl.Fact => d }
  def states: List[Decl.State] = decls.collect { case d: Decl.State => d }
  def calls: List[Decl.Call] = decls.collect { case d: Decl.Call => d }
  def rules: List[Decl.Rule] = decls.collect { case d: Decl.Rule => d }
  def counts: List[Decl.Count] = decls.collect { case d: Decl.Count => d }

/** A FILE OF TESTS, beside its policy: `tests for payments`, then its tests */
final case class TestFile(policy: String, tests: List[Decl.Test], pos: Pos)
