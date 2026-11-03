package okay.policy

import okay.datalog as dl
import okay.proof.{Infer, Kernel, Sort}
import okay.scala3.*

import scala.util.Random

/** derived relations, certified (specs/policy.md, "Derived relations"): okay-datalog computes, the kernel re-derives */
class DeriveSuite extends munit.FunSuite:

  private val (user, group) = (Sort.Named("User"), Sort.Named("Group"))
  private val groups = dl.Parse.program("""
    member(U, G) :- in_group(U, G).
    member(U, G) :- member(U, H), subgroup(H, G).
  """).toOption.get
  private val sorts = Map("in_group" -> List(user, group), "subgroup" -> List(group, group),
    "member" -> List(user, group))
  private val derive = Derive("groups", groups, sorts)
  private val kernel = Kernel(derive.theory)
  private def f(p: String, as: String*) = dl.Fact(p, as.toVector)

  private val tables = Vector(f("in_group", "ann", "devs"), f("subgroup", "devs", "eng"),
    f("subgroup", "eng", "staff"), f("in_group", "bob", "ops"), f("subgroup", "ops", "staff"))

  private def proved(result: dl.Result, fact: dl.Fact, k: Kernel = kernel) =
    run(Infer.by(k)(derive.prove[Infer](result, fact)))

  test("a derived fact a theorem: its conclusion the fact, its hypotheses exactly the facts the derivation used"):
    val r = derive.run(tables).toOption.get
    val goal = f("member", "ann", "staff")
    val thm = proved(r, goal).fold(e => fail(e), identity)
    assertEquals(thm.concl, derive.formula(goal))
    assertEquals(thm.hyps, Set(f("in_group", "ann", "devs"), f("subgroup", "devs", "eng"),
      f("subgroup", "eng", "staff")).map(derive.formula))                       // nothing of bob's
    assert(kernel.owns(thm))

  test("the axioms: a rule's variables the head's first, the others of its body ∀ too"):
    val ax = derive.axioms(1)
    assertEquals(ax.vars.map(_.name), List("U", "G", "H"))
    assert(ax.formula.toString.contains("member(U, H)"), ax.formula.toString)

  test("what is not derived has no theorem"):
    val r = derive.run(tables).toOption.get
    assert(proved(r, f("member", "ann", "ops")).isLeft)

  test("a kernel of another theory refuses the proof: the steps are checked, Derive is not trusted"):
    val wrong = Derive("groups", dl.Parse.program("""
      member(U, G) :- in_group(U, G).
      member(U, G) :- member(U, H), in_group(U, G).
    """).toOption.get, sorts)
    // the same axiom names, a different second rule: the kernel of that theory
    val forged = Kernel(okay.proof.Theory("groups", derive.axioms.head.name -> derive.axioms.head.formula,
      derive.axioms(1).name -> wrong.axioms(1).formula))
    val r = derive.run(tables).toOption.get
    assert(proved(r, f("member", "ann", "staff"), forged).isLeft)
    assert(proved(r, f("member", "ann", "devs"), forged).isRight)               // the first rule is the same

  test("every fact okay-datalog derives is proved, on random hierarchies"):
    val rnd = Random(11)
    for round <- 1 to 25 do
      val gs = (0 until 2 + rnd.nextInt(10)).map(i => s"g$i")
      val us = (0 until 1 + rnd.nextInt(5)).map(i => s"u$i")
      val ts = (for a <- gs; b <- gs if a != b && rnd.nextDouble() < 0.2 yield f("subgroup", a, b)) ++
        (for u <- us; g <- gs if rnd.nextDouble() < 0.2 yield f("in_group", u, g))
      val r = derive.run(ts).toOption.get
      for t <- r.relation("member") do
        val goal = dl.Fact("member", t)
        val thm = proved(r, goal).fold(e => fail(s"round $round, $goal: $e"), identity)
        assertEquals(thm.concl, derive.formula(goal))
        assert(thm.hyps.subsetOf(ts.map(derive.formula).toSet), s"round $round: a hypothesis not a table fact")
