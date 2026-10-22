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
`¬¬f` gives `f`), reflexivity and substitution of equals, induction over the integers from 0. Small enough to read in
one sitting, universal enough for arithmetic statements about every number (`InductionSuite`: `∀n. 0 ≤ n → 0 ≤
sum(n)`).

## Proofs as programs, steps as an effect

`Infer.Step(rule)` is an operation; `Infer.by(kernel)` the handler that answers it. A proof written as a program —
or found by `Auto`, the proof search: backward from the goal through the theory's rules, the facts binding what the
goal does not, a term of one's own replaced by its value from a fact, the alternatives a `Choose` (the handler is the
strategy: `first`, `all`) — goes through any interceptor of okay-simple's: `observe` sees every step (an audit of the
proof), `around` refuses a rule or answers from a cache. None can forge a theorem: [docs/trust.md](docs/trust.md).

## Speed

A decision proved — transfer allowed under the policy, 25 steps, found by the search on effects — in about 8 µs;
refused (every branch tried) in about 5 µs; one step 20–300 ns; exact money arithmetic 100 ns a step. A certificate:
about 18 µs to write (2.9 KB), 26 µs to check (every step derived again). `sbt "Test/runMain okay.proof.Bench"`
(JDK 26, Apple silicon, the median of five rounds).

## Build

Scala 3.3 LTS; depends on okay-simple's release (`io.github.okay-effects::okay-effects-machine:0.1.0`, from its
Maven repository on GitHub Pages).

```
sbt test                                  # the kernel's rules, effects and forging, the policy, induction, certificates
sbt "Test/runMain okay.proof.Bench"       # what it costs at run time
```

## Not yet

Linear arithmetic over variables (a decision procedure: the kernel computes only closed formulas), equational
rewriting at scale, a library of arithmetic lemmas, a second checker of certificates in another language (okay-lean's
wire could carry them), proofs about Scala code itself (a macro reading definitions).

License: Apache 2.0.
