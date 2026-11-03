package okay.policy

import okay.proof.{Certificate, Kernel}
import okay.scala3.*

/** derived relations in the language (specs/policy.md, "Derived relations"): `derive` over `table` facts, computed by
 * okay-datalog, every step of a decision's derived atom re-derived in the kernel */
class DerivedSuite extends munit.FunSuite:

  val text = """policy groups

type User
type Group

fact in_group(user: User, group: Group) table
fact subgroup(group: Group, parent: Group) table

derive member(user: User, group: Group)
  from in_group(user, group)
  from member(user, g), subgroup(g, group)

call admin.reset(target: Text)

allow admin.reset when member(caller, admins)
"""
  val tests = """tests for groups

test "a member through the hierarchy may"
  given in_group(ann, devs), subgroup(devs, eng), subgroup(eng, admins), in_group(bob, ops)
  when ann calls admin.reset(target: "db")
  expect allow

test "not a member may not"
  given in_group(bob, ops), subgroup(devs, admins)
  when bob calls admin.reset(target: "db")
  expect deny
"""
  val policy = Compiled(text).fold(ps => fail(ps.mkString("\n")), identity)
  val (ann, bob) = (Value.E("User", "ann"), Value.E("User", "bob"))
  def g(n: String) = Value.E("Group", n)
  val facts = Map(
    FactRef("in_group", List(ann, g("devs"))) -> Answer.Holds(true),
    FactRef("subgroup", List(g("devs"), g("eng"))) -> Answer.Holds(true),
    FactRef("subgroup", List(g("eng"), g("admins"))) -> Answer.Holds(true),
    FactRef("in_group", List(bob, g("ops"))) -> Answer.Holds(true))
  type Row[X] = (States + Facts)[X]
  def decide(by: Value, known: Map[FactRef, Answer] = facts) =
    run(States.Memory(policy.checked).handler(Facts.known(known)(
      Decide[Row](policy, Call.flat("admin.reset", by, Map("target" -> Value.T("db")))))))

  test("written and read back: `table` and `derive` round trip"):
    val p = Parser.parse(text).fold(e => fail(e.toString), identity)
    assertEquals(Parser.parse(Printer(p)).map(Printer(_)), Right(Printer(p)))
    assert(Printer(p).contains("fact in_group(user: User, group: Group) table"), Printer(p))
    assert(Printer(p).contains("from member(user, g), subgroup(g, group)"), Printer(p))

  test("the tests pass"):
    val outcomes = Tests.run(policy, tests).fold(ps => fail(ps.mkString("\n")), identity)
    assert(outcomes.forall(_.passed), outcomes.mkString("\n"))

  test("ALLOW by a derived fact: a theorem whose hypotheses are exactly the table facts the derivation used"):
    val d = decide(ann)
    assertEquals(d.verdict, Verdict.Allow)
    val t = d.theorem.get
    assert(policy.kernel.owns(t))
    assertEquals(t.hyps.map(_.toString), Set("in_group(ann, devs)", "subgroup(devs, eng)", "subgroup(eng, admins)"))
    assert(Certificate.check(d.certificate.get, Kernel(policy.theorize.theory)).isRight)

  test("no derivation, no allow: the default deny says the derived atom is false"):
    val d = decide(bob)
    assertEquals(d.verdict, Verdict.Deny)
    assertEquals(d.theorem, None)
    assert(d.reasons.exists(_.contains("member(bob, admins) is false")), d.reasons.toString)

  test("the checker: tables only, variables of agreeing sorts, every head variable bound, no `not` of a derived one"):
    def problems(body: String): List[String] = Types(text.replace("allow admin.reset when member(caller, admins)",
      body)) match
      case Left(ps) => ps.map(_.message)
      case Right(_) => Nil
    assert(problems("fact owns(user: User, group: Group)\nderive o(u: User, x: Group)\n  from owns(u, x)")
      .exists(_.contains("reads tables")))
    assert(problems("derive m2(u: User, x: Group)\n  from in_group(u, y)").exists(_.contains("x is not bound")))
    assert(problems("derive m3(u: User, x: Group)\n  from in_group(u, x), subgroup(u, x)")
      .exists(_.contains("u is User and Group")))
    assert(problems("allow admin.reset when not member(caller, admins)").exists(_.contains("under `not`")))
    assert(problems("fact n(user: User): Int table").exists(_.contains("a table is a relation")))
