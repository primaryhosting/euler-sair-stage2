# EULER — Statement-Fidelity Record
*(the paper's §8 protocol, applied to a live submission — including two
fidelity failures we caught in our own tooling, which are the §8 argument
made empirical)*

The paper's claim: formal verification adjudicates statement→proof and is
silent on problem→statement; no procedure operating solely on a proposition
and its proof can certify fidelity to the prior informal intention. The
five mechanisms below don't close that gap; they make the residual judgment
explicit. Here is each, as practiced in this submission.

---

## 1. Formalization contract

**Informal problem** (competition prose): given two equational laws over a
single binary operation, decide whether every magma satisfying the first
satisfies the second; FALSE answers must exhibit a finite magma.

**Formal statement** (the judge's, published in the open repository —
adjacent here as the contract requires):

```lean
class Magma (α : Type _) where op : α → α → α
@[inherit_doc] infix:65 " ◇ " => Magma.op
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (…vars… : G), <eq1>
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (…vars… : G), <eq2>
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
```

Two fidelity observations worth stating rather than assuming:
- The formal statement quantifies over **all types with a magma structure**,
  including infinite ones — faithful to "every magma," with no hidden
  finiteness restriction.
- The FALSE certificate shape (`Fin n` table + `decideFin!`) is *narrower*
  than the informal "exhibit a counterexample": implications refutable only
  by infinite models cannot be certified FALSE in this format. This is the
  organizers' rendering decision, not ours; we record it because our two
  unresolved public FALSE pairs may live exactly in that gap.

## 2. Semantic change log (every rendering decision between problem text and Lean)

| Decision | Rendering | Risk if silent |
|---|---|---|
| Operator symbol | Problem files write `*`; the judge's Lean defines only `◇`. All solver emission normalizes `*` → `◇`. | **Realized — see §3, failure B.** |
| Variable binding | Binders in first-appearance order, explicitly typed `(x y z : G)`; goal introduces LHS variables then unseen RHS variables. | Wrong binder order silently changes which theorem is proved. |
| Precedence | `◇` at `infix:65`, left-associative; all emitted terms fully parenthesized so no proof depends on precedence. | A dropped parenthesis proves a different equation. |
| Hypothesis instantiation | `h a b c` applies the law at explicit terms; compound instantiations (e.g. `h (x◇y) z w`) are the workhorse of the chain provers. | None — but it is where most emitted-proof content lives, so it is stated. |
| FALSE semantics | Python pre-check evaluates *all* assignments over `Fin n` (`decideFin!` semantics, no sampling). | A sampled check could emit a table the judge refutes. |
| Judge-goal replica (dev-time Axle) | Bare `Magma`, named `EquationLHS/RHS`, `infix:65`, no Mathlib — rebuilt to match the judge's `JudgeProblem` exactly after failure A below. | **Realized — see §3, failure A.** |

## 3. Adversarial statement review — two caught failures, on the record

The paper argues most fidelity failures are invisible because nobody writes
them down. We write ours down; they are the strongest evidence in this pack
that the layer is real.

**Failure A (2026-08-21): the hand-built goal that wasn't the judge's.**
An earlier dev-time verifier constructed its own version of the implication
goal. Its variable-binding convention differed subtly from the judge's
`JudgeProblem`. Result: proofs our verifier accepted were **rejected by the
real judge** ("unsolved goals"; "introN failed") — verified-against-the-wrong-
statement, the exact underdetermination §8 describes. Remedy: the replica
was rebuilt from the judge's published source and re-validated. Every
"verified" claim in this pack postdates that rebuild.

**Failure B (2026-08-25): the operator glyph.**
The evaluation files write the operation as `*`; our verification wrapper
interpolated equation text verbatim into a Lean preamble defining only `◇`.
Lean then demanded a `Mul` instance that does not exist and rejected **five
mathematically-correct proofs** (`synthInstanceFailed`). For one measurement
cycle the record showed 0/7 where the truth was 5/7. The failure was in the
*statement rendering*, not the mathematics — and it was found only because
the protocol here treats "why did verification fail" as a question about the
statement before it is a question about the proof. Remedy: operator
normalization at the wrapper boundary; re-run flipped exactly the five
mathematically-solved cases to verified.

Both episodes are §8's thesis in miniature: *the proof checker was working
perfectly both times.* What failed was fidelity between the statement we
checked and the statement we intended.

## 4. Dual formalization

Two independently produced routes to the same acceptance criterion:
- the **official judge modules** (open repository, Lean v4.32.2, pinned
  commit), and
- the **dev-time replica** used for measurement (rebuilt from the judge's
  source after failure A).

Divergence between them is treated as an alarm, not noise — both recorded
failures above were *found* as divergences. Additionally, every FALSE
witness is checked in two semantics: a Python full finite evaluation and
Lean's `decideFin!`.

## 5. Boundary testing

- **Held-out sampling:** 120 order-4 FALSE pairs excluded from every
  released set, and 100 whose *hypothesis* never appears in any released
  set — all solved and self-checked (guards against the bank being fitted to
  the released statements).
- **Distribution boundary:** the order-5 evaluation set lies entirely
  outside the direction oracle; measuring there (190/200 organically)
  bounds behavior beyond the embedded table's domain.
- **Adversarial self-test:** the emission provers were run on seeded random
  problem streams; the const-collapse template bug was found exactly this
  way (18 invalid emissions on one seed), then fixed to be
  correct-by-construction and re-tested on unseen seeds (0 invalid).

## 6. The failure class the protocol does not catch — named here as the paper requires

§8 names honest-verified-empty formalizations (tautological loops) as
uncaught by all five mechanisms. Our exposure to that class is structurally
limited — the target statements are fixed by the competition, not chosen by
us — but the adjacent risk exists and is disclosed in `5-EPISTEMIC-BADGES.md`:
a **pair-keyed certificate** is fidelity-perfect for its released public row
and *contentless about unseen rows*. We therefore never count those
certificates as generalization evidence, and the badge table marks them
separately from the tiers that generalize.
