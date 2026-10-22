# okay-proof

A small prover for the run time: a kernel of first-order logic with equality, induction and EXACT ARITHMETIC BY
COMPUTATION, LCF-style (a theorem is a value only the kernel makes), whose inference steps are also an EFFECT of
[okay-simple](https://github.com/okay-effects/okay-simple)'s — so a proof can be audited step by step and controlled by
interceptors without trusting them. Built for decisions that must be justified: a transfer allowed by a policy, a sum
of money computed with its rounding named, a limit respected — each a theorem, its certificate checkable again
elsewhere.

```scala
import okay.proof.*
import okay.proof.Formula.*

val k = Kernel(Bank.policy)                         // the policy: axioms, ∀u r a amt. … implies mayTransfer(u, a, amt)
Auto.prove(k, Bank.facts, Bank.transfer(Bank.ann, Bank.acc1, "500.00")) match
  case Right(Some(t)) =>                             // t: Thm — hypotheses ⊢ mayTransfer(ann, acc1, 500.00)
    t.hyps                                           // exactly the request's facts it rests on
    Certificate.of(t)                                // JSON, checked again by Certificate.check(json, kernel)
  case Right(None) => ()                             // not allowed: no proof
  case Left(why) => ()                               // a step was refused (a veto of an interceptor)
```

(`Bank` is the tests' vocabulary, `src/test/scala/okay/proof/Vocabulary.scala`.)

## The logic

Many-sorted first-order logic: sorts `Int` (unbounded), `Dec` (exact decimals), `Str` and one's own
(`Sort.Named("Account")`); functions and predicates of one's own, known by axioms and facts; the kernel's functions
(`Fns`: `+ - * neg div mod`, `dec d+ d- d* d/`, `round` half to even, `roundHalfUp`, `++ length`), computed. Formulas:
`True False = < ≤`, predicates, `¬ ∧ ∨ →`, `∀ ∃`. In Scala: `a && b implies c` is `(a ∧ b) → c` (a word, so it binds
the loosest).

The rules (`Rule`, checked by `Kernel.derive`): assumption, axiom, `Compute` (a closed formula of the kernel's
functions, evaluated: true in one step), introduction and elimination of each connective and quantifier (classical:
`¬¬f` gives `f`), reflexivity and substitution of equals, induction over the integers from 0, and four that check
LINEAR ARITHMETIC by certificate: `Norm` (an identity: `x + y = y + x`, `x ≤ x + 1`), `LinComb` (non-negative
multiples of inequalities summed — Farkas'), `Antisym`, `Tighten` (the integers' rounding of a bound), and two of
ordered rings, `MulNonneg` and `Square`. Small enough to
read in one sitting, universal enough for arithmetic statements about every number (`InductionSuite`: `∀n. 0 ≤ n →
0 ≤ sum(n)`, its steps by linear arithmetic, with no axiom about addition).

## Arithmetic: linear, the integers, products

`Linarith` decides a comparison over `Int` or `Dec` from facts and theorems: `x ≤ y, y ≤ z ⊢ x ≤ z`; `spent(ann) ≤
300.00, daily(teller) = 1500.00 ⊢ spent(ann) + 900.00 ≤ daily(teller)`; `x = y + 1, y = 3 ⊢ x = 4`. It refutes the
negated goal, and what it finds is a certificate the kernel checks (`LinComb`, `Compute`, …): the procedures are
trusted for nothing.

- **Over the rationals** (`Dec`): Fourier–Motzkin elimination — complete.
- **Over the integers** (`Int`): the same with the integers' tightening first, then the **Omega test** (Pugh): exact
  elimination where it can, a fresh `σ` for an equation with no coefficient ±1 (`mod̂`), and otherwise the dark shadow
  or the grey shadow's splinters, each a case — complete for linear constraints. `27 ≤ 11x + 13y ≤ 45, −10 ≤ 7x − 9y ≤
  4` has rational solutions and no integer one: refuted. Checked against brute force on 600 random systems, 300 of
  them thin crossing strips where the rationals' elimination is not enough.
- **Products of variables**: a term is a polynomial (`Norm` proves ring identities, `(x+y)² = x² + 2xy + y²`); the
  kernel knows that products of non-negatives are non-negative (`MulNonneg`) and squares are (`Square`); the search
  adds the premises' pairwise products and the atoms' squares, as Mathlib's `nlinarith` does: `0 ≤ x, 0 ≤ y ⊢ 0 ≤
  x·y`, `2 ≤ x ⊢ 4 ≤ x·x`, `0 ≤ p ≤ 10.00, 0 ≤ q ≤ 5 ⊢ p·q ≤ 50.00`. Sound, not complete (nothing can be, over the
  integers).

Terms of one's own are atoms (`limit(teller)`, `sum(x)`). `Auto` uses all of it for every comparison a fact does not
settle by its value.

`Lemmas(kernel)`: a library of general theorems — the orders (`leTrans`, `ltLeTrans`, `leTotal`, `notLe`, …),
addition (`addComm`, `addAssoc`, `addLeAdd`, `addNonneg`, …) over `Int` and `Dec`, the integers' (`ltSuccLe`),
equality for any sort (`eqSym`, `eqTrans`), the classical schemas for any formulas (`excludedMiddle`,
`contrapositive`, `deMorganAnd`, `deMorganOr`) — each PROVED by the kernel when first asked for, and kept: the
trusted base does not grow.

## Proofs as programs, steps as an effect

`Infer.Step(rule)` is an operation; `Infer.by(kernel)` the handler that answers it. A proof written as a program —
or found by `Auto`, the proof search: backward from the goal through the theory's rules, the facts binding what the
goal does not, a term of one's own replaced by its value from a fact, the alternatives a `Choose` (the handler is the
strategy: `first`, `all`) — goes through any interceptor of okay-simple's: `observe` sees every step (an audit of the
proof), `around` refuses a rule or answers from a cache. None can forge a theorem: [docs/trust.md](docs/trust.md).

## Certificates, and a second checker

`Certificate.of(t)` writes a theorem's proof as JSON: the theory BY VALUE (`axioms`) with its DIGEST (FNV-1a, 64 bits,
of the axioms' JSON), the steps in order, the claimed conclusion and hypotheses. `Certificate.check(json, kernel)`
derives every step again under a kernel whose theory is the one carried; `Certificate.checkAlone(json)` under the
theory it carries — what that theory says is an auditor's to judge, its digest pins it.

A SECOND CHECKER, independent: okay-lean's `okay-check` — this kernel written again in Lean — checks the same
certificates. `DifferentialSuite` makes 106 proofs of every kind (transfer decisions, linear arithmetic, the Omega
test's 1016-step refutation, products, induction, the 42 lemmas, each of the 28 rules at least once) and 700 mutants
of them (a number, a premise, a coefficient, a rule, a step dropped, the conclusion, a hypothesis, the digest, an
axiom), and both kernels must give every one the same verdict: 140 accepted and 666 refused by both. Runs when
`okay-check` is built (`OKAY_LEAN`, by default `~/work/my/okay-lean`).

## Speed

| | |
|---|---|
| a decision proved: transfer allowed under the policy, 25 steps, found by the search on effects | 7.4 µs |
| refused: every branch tried | 4.5 µs |
| from bounds, `spent(ann) ≤ 300.00`, by linear arithmetic | 12.6 µs |
| linear arithmetic: a chain of three, over `Int` | 10.2 µs |
| over `Int`, `2x = 1` refuted, a tightening in it | 5.3 µs |
| an equation over `Dec` (two refutations) | 17.5 µs |
| the Omega test: `3x + 5y = 1` in a box (a fresh `σ`) | 60 µs |
| the Omega test: Pugh's example, ~1000 steps, by cases | 1.9 ms |
| products: `0 ≤ p ≤ 10, 0 ≤ q ≤ 5 ⊢ p·q ≤ 50` | 107 µs |
| one step | 20–360 ns |
| exact money arithmetic, a step | 110 ns |
| the lemma library, 42 lemmas proved | 276 µs, once |
| a certificate written (2.9 KB) / checked, every step derived again | 14 µs / 27 µs |

`sbt "Test/runMain okay.proof.Bench"` (JDK 26, Apple silicon, the median of five rounds).

## Build

Scala 3.3 LTS; depends on okay-simple's release (`io.github.okay-effects::okay-effects-machine:0.1.0`, from its
Maven repository on GitHub Pages).

```
sbt test                                  # 56 (with okay-lean's checker built): the kernel's rules, linear arithmetic, lemmas, effects and forging, the policy, induction, certificates
sbt "Test/runMain okay.proof.Bench"       # what it costs at run time
```

## Not yet

Products beyond degree two of the premises, real-closed fields (a complete decision for `Dec` with products: CAD),
rewriting at scale, the second checker's rules proved sound in Lean, proofs about Scala code itself (a macro
reading definitions).

License: Apache 2.0.
