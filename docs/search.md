# Proof search: `Auto`

`Auto.prove(kernel, facts, goal)` proves `goal` backward from FACTS (the hypotheses: what a request brings) and the
theory's RULES (its axioms `∀x̄. body → head`, or `∀x̄. head`). Each inference a step of `Infer` — checked by the
kernel, seen by any interceptor; each alternative a choice of okay-simple's `Choose`, so the handler is the strategy:
`first` (the first proof, depth first — `Auto.prove`), `all` (every one).

A goal is, in turn:

1. a fact: `assume`;
2. closed and computable: `compute` if true, and a branch that ends if false;
3. a conjunction: both; a disjunction: a side, chosen;
4. a formula with a term of one's own whose value a fact gives (`balance(acc1) = 250.00`): rewritten, then proved;
5. a comparison over `Int` or `Dec`: `Linarith` over the facts (bounds, not only values);
6. the head of a rule: its variables bound by the head, the rest by facts matching its body, the body then proved.

The result's hypotheses are the facts it used — exactly what the decision rests on.

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val Role = Sort.Named("Role")
val User = Sort.Named("User")
def const(name: String, sort: Sort): Term = Ap(Fn(name, Nil, sort), Nil)
val (ann, bob, teller) = (const("ann", User), const("bob", User), const("teller", Role))
val hasRole = Pred("hasRole", List(User, Role))
val mayApprove = Pred("mayApprove", List(User, Sort.Dec))
val limit = Fn("limit", List(Role), Sort.Dec)
val (u, r, amt) = (V("u", User), V("r", Role), V("amt", Sort.Dec))
val rules = Theory("approvals",
  "approve" -> Formula.all(u, r, amt)(
    P(hasRole, List(u, r)) && Le(amt, Ap(limit, List(r))) implies P(mayApprove, List(u, amt))))
val k = Kernel(rules)
val facts = List(P(hasRole, List(ann, teller)), Le(D(BigDecimal("1000")), Ap(limit, List(teller))))

// r is not in the goal: the fact hasRole(ann, teller) binds it; the limit is only bounded below: linear arithmetic
val Right(Some(t)) = Auto.prove(k, facts, P(mayApprove, List(ann, D(BigDecimal("400"))))): @unchecked
assert(t.hyps == facts.toSet)
assert(Auto.prove(k, facts, P(mayApprove, List(bob, D(BigDecimal("400"))))) == Right(None))   // no role
```

A bound that does not settle it is no proof: with the limit known only to be at most 1000, nothing follows about
400 ≤ limit(teller):

```scala
val bounded = List(P(hasRole, List(ann, teller)), Le(Ap(limit, List(teller)), D(BigDecimal("1000"))))
assert(Auto.prove(k, bounded, P(mayApprove, List(ann, D(BigDecimal("400"))))) == Right(None))
```

## By hand, on effects

`Auto(theory, facts).prove[R](goal)` is a program over any row with `Infer` and `Choose`; `Auto.prove` runs it under
`first` and the kernel. Another handler of `Choose` is another strategy — `all` gives every proof.
