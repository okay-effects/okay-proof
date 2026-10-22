# Lemmas

`Lemmas(kernel)`: general theorems — closed, quantified — PROVED by the kernel (the arithmetic ones by `Linarith`'s
certificates, the rest by natural deduction), each when first asked for, and kept. Not axioms: the trusted base does
not grow, and a lemma is a theorem of its kernel only.

| | over `Int` and `Dec` |
|---|---|
| order | `leRefl`, `leTrans`, `ltLeTrans`, `leLtTrans`, `ltIrrefl`, `ltToLe`, `leAntisym`, `notLe`, `notLt`, `leTotal` |
| addition | `addComm`, `addAssoc`, `addZero`, `subSelf`, `addLeAdd`, `addNonneg`, `subNonneg` |
| the integers | `ltSuccLe` (`x < y → x + 1 ≤ y`), `leOfLtSucc` |
| equality, any sort | `eqRefl`, `eqSym`, `eqTrans` |
| classical, any formulas | `excludedMiddle`, `contrapositive`, `deMorganAnd`, `deMorganOr` |

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val k = Kernel(Theory.empty)
val lemmas = Lemmas(k)
val trans = lemmas.leTrans(Sort.Int)           // ∀x y z. x ≤ y ∧ y ≤ z → x ≤ z
def ok(r: Rule): Thm = k.derive(r).toOption.get
val inst = ok(Rule.AllE(ok(Rule.AllE(ok(Rule.AllE(trans, I(1))), I(2))), I(3)))
val used = ok(Rule.ImpE(inst, ok(Rule.Compute(And(Le(I(1), I(2)), Le(I(2), I(3)))))))
assert(used.concl == Le(I(1), I(3)))
assert(lemmas.all.forall((_, t) => t.hyps.isEmpty && k.owns(t)))
val open_ = P(Pred("open", Nil), Nil)
assert(lemmas.excludedMiddle(open_).concl == Or(open_, Not(open_)))
```

A lemma is also a theorem to give `Linarith.decide(kernel, goal, facts, theorems)`.
