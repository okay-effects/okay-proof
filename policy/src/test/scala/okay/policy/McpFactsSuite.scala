package okay.policy

import okay.proof.Json
import okay.scala3.*
import okay.scala3.std.*

import scala.concurrent.{ExecutionContext, Future}

/** facts fetched by MCP tools: the guard's own call, its arguments from the fact's, its value at a path */
class McpFactsSuite extends munit.FunSuite:
  given ExecutionContext = Async.defaultContext

  val text = """policy refunds
    |type User
    |type Account
    |fact balance(account: Account): Dec from mcp stripe.retrieve_balance(customer: account,
      currency: "eur") at "available.0.amount"
    |fact vip(user: User) from mcp crm.get_customer(id: user) at "flags.vip"
    |call stripe.refund(account: Account, amount: Dec)
    |allow stripe.refund when amount <= balance(account) and vip(caller)
    |""".stripMargin
  val policy = Compiled(text).fold(ps => fail(ps.mkString("\n")), identity)
  val ann = Value.E("User", "ann")
  val call = Call.flat("stripe.refund", ann, Map("account" -> Value.E("Account", "cus_1"),
    "amount" -> Value.D(BigDecimal(40))))

  type Row[X] = (Async + States + Facts)[X]
  def decide(invoke: (String, Json) => Future[Json]) =
    val sources = Source.mcp(policy.checked, invoke)
    Async.toFuture(States.Memory(policy.checked).handler(Facts.from(policy.checked, sources)(Decide[Row](policy,
      call))))

  def structured(j: String) = Json.parse(s"""{"structuredContent": $j}""").toOption.get
  def texted(j: String) = Json.Obj(List("content" -> Json.Arr(List(Json.Obj(List("type" -> Json.Str("text"),
    "text" -> Json.Str(j)))))))

  test("written and read again; a fetch's arguments are the fact's parameters or literals") {
    val printed = Printer(Parser.parse(text).toOption.get)
    val fetch = """from mcp stripe.retrieve_balance(customer: account, currency: "eur") at "available.0.amount""""
    assert(printed.contains(fetch), printed)
    assertEquals(Printer(Parser.parse(printed).toOption.get), printed)
    assertEquals(Facts.missing(policy.checked, Source.mcp(policy.checked, (_, _) => Future.never).keySet), Set.empty)
    assertEquals(Types(text.replace("customer: account", "customer: acct")).left.map(_.map(_.message)),
      Left(List("an unknown name acct")))
  }

  test("each fact by its tool, with its arguments; the value at the path — structured or a text of JSON") {
    val asked = scala.collection.mutable.ListBuffer.empty[(String, String)]
    decide { (tool, args) =>
      asked += tool -> args.render
      Future.successful(tool match
        case "stripe.retrieve_balance" => structured("""{"available": [{"amount": 100.50}]}""")
        case _ => texted("""{"flags": {"vip": true}}"""))
    }.map { d =>
      assertEquals(d.verdict, Verdict.Allow, d.reasons.toString)
      assertEquals(asked.toSet, Set("stripe.retrieve_balance" -> """{"customer":"cus_1","currency":"eur"}""",
        "crm.get_customer" -> """{"id":"ann"}"""))
      assert(d.facts.map(_.toString).exists(_.startsWith("balance(cus_1) = 100.5")), d.facts.toString)
    }
  }

  test("a tool failing, a path to nothing, a value of another kind: unknown — denied") {
    for
      failing <- decide((_, _) => Future.failed(IllegalStateException("down")))
      nowhere <- decide((t, _) => Future.successful(structured("""{"available": []}""")))
      wrong <- decide((t,
        _) => Future.successful(structured("""{"available": [{"amount": "lots"}], "flags": {"vip": "yes"}}""")))
    yield for d <- List(failing, nowhere, wrong) do assertEquals(d.verdict, Verdict.Deny, d.reasons.toString)
  }
