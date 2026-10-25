package okay.policy

import okay.proof.{Certificate, Json, Kernel}
import okay.scala3.*

/** calls with records, lists and optional arguments: checked, decided, each decision proved */
class StructuredSuite extends munit.FunSuite:
  val shop = """policy shop
    |type User
    |type Item = { sku: Text, qty: Int, price: Dec, note?: Text }
    |type Address = { country: Text, zip?: Text }
    |fact blocked(sku: Text)
    |call shop.order(items: List[Item], shipping: Address, coupon?: Text, tags: List[Text])
    |
    |allow shop.order
    |  when count(items) <= 3
    |   and every i in items: (i.qty <= 10 and i.price <= 500.00 and not blocked(i.sku))
    |   and shipping.country in ["DE", "PL"]
    |   and (not has(coupon) or coupon starts "VIP")
    |   and not (some t in tags: t = "test")
    |ask shop.order
    |  when some i in items: i.price > 500.00
    |  because "an expensive item"
    |""".stripMargin
  val policy = Compiled(shop).fold(ps => fail(ps.mkString("\n")), identity)
  val ann = Value.E("User", "ann")

  def item(sku: String, qty: Int, price: String, note: Option[String] = None): Data = Data.Rec(Map(
    "sku" -> Data.Leaf(Value.T(sku)), "qty" -> Data.Leaf(Value.I(qty)), "price" -> Data.Leaf(Value.D(BigDecimal(price))))
    ++ note.map(n => "note" -> Data.Leaf(Value.T(n))))
  def order(items: List[Data], country: String = "DE", coupon: Option[String] = None, tags: List[String] = Nil) =
    Call("shop.order", ann, Map("items" -> Data.Lst(items),
      "shipping" -> Data.Rec(Map("country" -> Data.Leaf(Value.T(country)))),
      "tags" -> Data.Lst(tags.map(t => Data.Leaf(Value.T(t))))) ++ coupon.map(c => "coupon" -> Data.Leaf(Value.T(c))))
  val notBlocked = (skus: List[String]) => skus.map(s => FactRef("blocked", List(Value.T(s))) -> Answer.Holds(false)).toMap

  type Row[X] = (States + Facts)[X]
  def decide(c: Call, facts: Map[FactRef, Answer] = notBlocked(List("a", "b", "c", "x"))) =
    run(States.Memory(policy.checked).handler(Facts.known(facts)(Decide[Row](policy, c))))

  test("EVERY: each element checked; proved by cases over the elements the call gave, as a closed list") {
    val d = decide(order(List(item("a", 2, "10.00"), item("b", 1, "99.50", Some("gift")))))
    assertEquals(d.verdict, Verdict.Allow, d.reasons.toString)
    val hyps = d.facts.map(_.toString)
    assert(hyps.exists(_.startsWith("∀")), hyps.toString) // the list, closed: ∀e. items(call, e) ⇒ e = #0 ∨ e = #1
    assert(hyps.exists(_.contains("Item.price")), hyps.toString)
    assert(hyps.exists(_.contains("¬blocked(\"a\")")), hyps.toString)
    assert(Certificate.check(d.certificate.get, Kernel(policy.theorize.theory)).isRight)
  }

  test("an empty list: every holds of it; a list too long, an element too dear, a blocked one: not allowed") {
    assertEquals(decide(order(Nil)).verdict, Verdict.Allow)
    assertEquals(decide(order(List.fill(4)(item("a", 1, "1.00")))).verdict, Verdict.Deny)
    val dear = decide(order(List(item("a", 1, "1.00"), item("x", 1, "900.00"))))
    assertEquals(dear.verdict, Verdict.Ask) // SOME: proved by its witness
    assertEquals(dear.reasons, List("an expensive item"))
    assert(dear.theorem.isDefined)
    val blocked = decide(order(List(item("a", 1, "1.00"))), Map(FactRef("blocked", List(Value.T("a"))) -> Answer.Holds(true)))
    assertEquals(blocked.verdict, Verdict.Deny)
  }

  test("OPTIONAL: missing, the rule asks has(...) and is fine; given, it is checked; a nested record's field") {
    assertEquals(decide(order(List(item("a", 1, "1.00")), coupon = Some("VIP-7"))).verdict, Verdict.Allow)
    assertEquals(decide(order(List(item("a", 1, "1.00")), coupon = Some("FREE"))).verdict, Verdict.Deny)
    assertEquals(decide(order(List(item("a", 1, "1.00")), country = "US")).verdict, Verdict.Deny)
    val withTest = decide(order(List(item("a", 1, "1.00")), tags = List("x", "test")))
    assertEquals(withTest.verdict, Verdict.Deny) // not some: every is not, by cases
  }

  test("a MALFORMED call is denied: a required field missing, a value of the wrong kind") {
    val noShipping = Call("shop.order", ann, Map("items" -> Data.Lst(Nil), "tags" -> Data.Lst(Nil)))
    val d = decide(noShipping)
    assertEquals(d.verdict, Verdict.Deny)
    assert(d.reasons.exists(_.contains("shipping is missing")), d.reasons.toString)
    val json = Json.parse("""{"items": [{"sku": "a", "qty": "two", "price": 1}], "shipping": {"country": "DE"},
      "tags": []}""").toOption.get
    val bad = decide(Call.fromJson(policy.checked, "shop.order", ann, json))
    assertEquals(bad.verdict, Verdict.Deny)
    assert(bad.reasons.exists(_.contains("qty is not a Int")), bad.reasons.toString)
  }

  test("from JSON, as an MCP call carries it: numbers and texts to their sorts, nulls as missing") {
    val json = Json.parse("""{"items": [{"sku": "a", "qty": 2, "price": "12.50", "note": null}],
      "shipping": {"country": "PL", "zip": "00-001"}, "coupon": null, "tags": ["new"]}""").toOption.get
    val d = decide(Call.fromJson(policy.checked, "shop.order", ann, json))
    assertEquals(d.verdict, Verdict.Allow, d.reasons.toString)
  }

  test("the checker: paths, lists, records, optional fields") {
    def problems(rule: String) = Types(shop + rule).left.toOption.toList.flatten.map(_.message)
    assertEquals(problems("allow shop.order when shipping.city = \"x\""), List("Address has no field city"))
    assertEquals(problems("allow shop.order when items.qty > 1"),
      List("a list's elements are reached by every or some, not by a path: items.qty"))
    assertEquals(problems("allow shop.order when every s in shipping: s = \"x\""), List("shipping is not a list"))
    assertEquals(problems("allow shop.order when shipping = \"x\""),
      List("shipping is a Address: a field of it, or has(shipping)"))
    assertEquals(problems("allow shop.order when count(shipping) > 1"), List("count of a list only: shipping"))
    assertEquals(problems("allow shop.order when every items in items: items.qty > 1"),
      List("items is taken: an element needs a name of its own"))
    assertEquals(problems("fact f(xs: List[Text])"), List("a fact's parameter xs is a number, a text or an entity, not List[Text]"))
  }

  test("tests write calls with records and lists, optional fields left out") {
    val tests = """tests for shop
      |test "a small order"
      |  given not blocked("a")
      |  when ann calls shop.order(items: [{ sku: "a", qty: 1, price: 5.00 }], shipping: { country: "DE" }, tags: [])
      |  expect allow
      |test "a dear one is asked"
      |  given not blocked("a")
      |  when ann calls shop.order(items: [{ sku: "a", qty: 1, price: 900.00 }], shipping: { country: "DE" }, tags: [])
      |  expect ask "an expensive item"
      |""".stripMargin
    val outcomes = Tests.run(policy, tests).fold(ps => fail(ps.mkString("\n")), identity)
    assert(outcomes.forall(_.passed), outcomes.mkString("\n"))
    assertEquals(Types.tests(policy.checked, tests.replace("qty: 1, price: 5.00", "price: 5.00")).left.map(_.map(_.message)),
      Left(List("the call's argument qty is missing")))
  }

  test("BOOL arguments: a condition by themselves; from JSON's true and false; a field the policy does not know, left out") {
    val p = Compiled("""policy files
      |type User
      |type Opts = { force: Bool, verbose?: Bool }
      |call fs.delete(path: Text, dry_run: Bool, opts: Opts)
      |allow fs.delete when dry_run or (not opts.force and path starts "/tmp/")
      |""".stripMargin).fold(ps => fail(ps.mkString("\n")), identity)
    def run(args: String) =
      val c = Call.fromJson(p.checked, "fs.delete", ann, Json.parse(args).toOption.get)
      okay.scala3.run(States.Memory(p.checked).handler(Facts.known(Map.empty)(Decide[Row](p, c))))
    assertEquals(run("""{"path": "/etc/x", "dry_run": true, "opts": {"force": true}, "extra": [1, 2]}""").verdict, Verdict.Allow)
    assertEquals(run("""{"path": "/tmp/x", "dry_run": false, "opts": {"force": false, "colour": "red"}}""").verdict,
      Verdict.Allow)
    assertEquals(run("""{"path": "/tmp/x", "dry_run": false, "opts": {"force": true}}""").verdict, Verdict.Deny)
    val bad = run("""{"path": "/tmp/x", "dry_run": "no", "opts": {"force": false}}""")
    assertEquals(bad.verdict, Verdict.Deny)
    assert(bad.reasons.exists(_.contains("dry_run is not a Bool")), bad.reasons.toString)
    assertEquals(Types("policy q\ntype User\ncall t(b: Bool)\nallow t when b = 1").left.map(_.map(_.message)),
      Left(List("b is a Bool: a condition by itself (`b`, `not b`), not a value")))
    assertEquals(Types("policy q\ntype User\nfact f(x: Bool)").left.map(_.map(_.message)), Left(List(
      "a fact's parameter x is a number, a text or an entity, not Bool (a relation fact is what is true or not)")))
  }

