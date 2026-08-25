# A Practitioner's Account
*Telling III — for formal-methods and automated-reasoning people*

---

You know the shape of this problem class, so I will spend the words where
practitioners spend attention: architecture, measurement, and the failures
that forced both.

## Task and adversary model

Instances are ordered pairs (E1, E2) of universally quantified single-axiom
identities over one binary operation. Decide E1 ⊨ E2 over the class of all
magmas; certify FALSE with a finite countermodel discharged by the judge's
`decideFin!`, certify TRUE with a Lean 4 proof of
`∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G`, kernel-checked by
SAIR's open deterministic judge (Lean v4.32.2, pinned commit; axioms
limited to `propext`, `Quot.sound`, `Classical.choice`; the `sorry` family,
metaprogramming, and unsafe primitives rejected by token and
dependency-closure audit). Sandbox: bare `python:3.11-slim`, 2 vCPU, 2 GB,
no network, one 500 KB source file, 3600 s per problem. The judge is the
score. Everything else is engineering under that constraint.

## Architecture: a refusal stack

**Direction is precomputed.** The ETP closure over the 4,694 order-4 laws
is embedded as a bitmatrix (~110 KB compressed; byte-identical to the
public `outcomes.json`, recomputed with zero disagreements). Validated
600/600 against the official evaluation answers. This deletes the
direction-classification problem on the core distribution — and the public
Stage-1 benchmark shows what it replaces: the best of 25 LLMs at 69%
direction accuracy on hard splits, most at base rate.

**FALSE side.** A 305-table finite-magma bank, orders 2–9, *keyed by
hypothesis*: at answer time the solver scans for a table satisfying E1 and
refuting E2. Because one magma satisfies many laws, coverage generalizes
far beyond the harvest — held-out measurement: 120/120 on pairs excluded
from every released set, 100/100 on pairs whose *hypothesis* never appears
in any released set. Bank misses fall to a pure-stdlib backtracking
finite-model search (orders 4–8, forward checking, restricted-growth
symmetry breaking). Every emitted table is exhaustively pre-checked in
`decideFin!` semantics — no sampling — before the judge re-proves it.

**TRUE side, cheapest first.**
1. *Certificate table*: 26 manual proofs, 390 proved dev-time by Harmonic's
   Aristotle, 18 ATP/loop-derived — all literal Lean bodies, all disclosed,
   all re-verified by the judge at answer time.
2. *Matching-chain search*: bidirectional rewrite chains, self-rechecked by
   re-walking every step before emission.
3. *Bounded Knuth–Bendix completion* ("mini-Twee", pure stdlib, embedded):
   derives critical-pair lemmas, emits explicit `have`-ladders. Two
   properties carry the design: emission is **total** — if it emits, the
   Lean is valid, achieved by making the const-collapse template
   correct-by-construction after a seeded-random audit found 18 invalid
   emissions — and **terminating**, via a hard deadline after a
   substitution-cycle nontermination was root-caused (a rule matching a
   subterm with permuted variables produced the cyclic substitution
   {a↦b, b↦a}; fix: one-pass simultaneous substitution).
4. *Transitivity*: factor i ⇒ j through provable intermediates. Licensed by
   a recomputed fact — the closure of the 10,657 public explicit-proof
   edges equals all 8,178,279 order-4 TRUE pairs exactly. Two-hop, then a
   bounded 3-hop meet-in-the-middle.
5. *ATP replay*: E's superposition proofs reconstructed node-by-node into
   named Lean `have`s (shared-DAG, so common subproofs are emitted once).
   The prover's derivation becomes the human-checkable artifact.
6. An LLM fallback exists, judge-gated, and on the core distribution is
   never reached.

**The invariant, which is the design:** every emit path terminates in an
independent check — full finite evaluation, chain re-walk, total emission,
or the kernel — and the judge gates every Solo answer besides. In the
Marathon track, which has *no* runtime judge (output is scored post-exit),
only self-verifying tiers are permitted to write at all. There is no path
from heuristic confidence to submitted answer.

## The case study: 1689 ⇒ 2391

Worth a practitioner's minute, because it locates the boundary between
search and insight precisely.

Every search tier failed — chain search saturated (correctly: the goal is
not reachable by rewriting), deep chain at depth 10/1500 s saturated in
seconds, two-hop transitivity starved on a measurable bottleneck (the
forward provable-edge frontier |A| ranged 1–7 against backward frontiers of
27–60; the lone 3-hop success in the residue had |A| = 19 — first-edge
provability, not path existence, was the constraint).

Completion, however, had derived a projection law: `L10 : ∀ a b, a = a◇b`
— reached through a short ladder (an absorption lemma L6:
`a ◇ ((a◇b)◇b) = a`, an idempotent-collapse L8, then L10 by a three-step
calc through the hypothesis). The finisher is not a rewrite and no rewrite
system will find it:

```
h a b a  :  a = (b◇a) ◇ ((a◇a)◇a)
L10      :  (b◇a) ◇ ((a◇a)◇a) = b◇a     (instantiated, symm)
⟹ a = b◇a ;  L10 b a : b = b◇a  ⟹  a = b        -- total collapse
```

`∀ a b, a = b` in hand, the goal is a single `exact`. The certificate —
completion scaffold, ALLEQ, one application; 3.9 KB — compiles under the
judge's exact toolchain. The general lesson: rewriting proves
*reachability*; collapse is a statement about the *model class*, and
crossing that categorical line took a human observation plus three lines.
The machine held the lemma; the human saw what it meant; the kernel
believed neither of them and checked.

## Measurement, with its inflation risks named

| Claim | Value | Status |
|---|---|---|
| Direction vs official answers (order-4) | 600/600 | Computationally verified |
| Released sets, 4 × 200 | 800/800 | **Ceiling** — leans on pair-keyed certs for released rows; organizers state those rows will not recur privately |
| Held-out FALSE (pairs / novel hypotheses) | 120/120 · 100/100 | Computationally verified |
| Order-5 set (fully outside the oracle) | 190/200 organic | Bounds worst-case beyond the table's domain |
| Official judge run | — | **None yet.** Last attempt hit an organizer-side olean mismatch, documented. One production run converts every ceiling. |

Two inflation risks were found and controlled, not discovered by a referee:
the FALSE bank's harvest *targeted* the released sets (hence the held-out
protocol above is the claim of record, not the released-set 100%), and the
released-set TRUE sweep leans on pair-keyed certificates (disclosed
per-pair, never counted as generalization).

Two fidelity failures are also on the record, and they are the most
instructive artifacts we own: a dev-time verifier whose hand-built goal
differed from the judge's binding convention — it *accepted* proofs the
judge rejected — and an operator-glyph mismatch (`*` vs `◇`) that
*rejected* five correct proofs with `synthInstanceFailed`. Both times the
checker was flawless; the statement it checked was not the statement
intended. If you take one thing from this document into your own practice,
take that layer: it is unguarded in every pipeline that does not guard it
explicitly.

## Tooling attribution, because provenance is load-bearing

ETP public data (Tao et al.) — direction and the transitivity license.
Axiom's **Axle** (Carina Hong's team) — dev-time compile-checks on the
judge's exact toolchain, ~2 s per certificate against a ~40-minute
playground loop; every certificate passed through it, and both fidelity
failures surfaced as Axle divergences. Harmonic's **Aristotle** — the 390
embedded Layer-1 proofs. Vampire (Kovács–Voronkov), E (Schulz), Mace4
(McCune) — the classical stack whose outputs the reconstruction pipeline
replays. Chain technique after the public Stage-2 leader, independently
reimplemented; Krympa-style reconstruction after Kondylidou et al. None of
these is a runtime dependency; all of them shaped what the runtime carries;
everything any of them produced was re-verified at least twice before the
judge saw it.

The formal account — precise statements, the verbatim derivations, and the
exact soundness argument — is Telling IV.
