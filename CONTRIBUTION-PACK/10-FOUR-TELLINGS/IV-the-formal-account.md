# The Formal Account
*Telling IV — sufficiency and necessity*

This document states exactly what is claimed, exhibits or cites the
derivation of each claim, and marks the trusted base of every verification.
Nothing is asserted that cannot be checked from the artifacts named here;
nothing needed for checking is omitted. Where a claim is *not* established,
that is stated with the same care.

---

## 1. Preliminaries

**Definition 1.** A *magma* is a pair (G, ◇) with ◇ : G × G → G. No axioms.

**Definition 2.** An *equational law* over variables V = {x, y, z, w, …} is
a pair of terms (s, t) in the signature {◇} over V, read as the sentence
∀V. s = t. A magma *satisfies* the law if the identity holds under every
assignment V → G.

**Definition 3 (the decision problem).** Given laws E1, E2: does every
magma satisfying E1 satisfy E2? Write E1 ⊨ E2. By Birkhoff's completeness
theorem for equational logic, E1 ⊨ E2 iff E2 is derivable from E1 by the
equational calculus (reflexivity, symmetry, transitivity, congruence,
substitution) — so semantic implication and syntactic derivability may be
used interchangeably below.

**Certificate formats (fixed by the competition).** FALSE: exhibit n ∈ ℕ
and t : Fin n × Fin n → Fin n with (Fin n, t) ⊨ E1 and (Fin n, t) ⊭ E2;
the judge re-decides both finite claims (`decideFin!`). TRUE: a Lean 4 term
of type `∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G`, where the
two predicates are the judge's @[reducible] renderings of E1, E2 with
per-variable binders. Trusted base of the judge: the Lean v4.32.2 kernel
(commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`), axioms at most
{`propext`, `Quot.sound`, `Classical.choice`}, token- and
dependency-closure audit rejecting the `sorry` family, metaprogramming, and
unsafe primitives.

**Remark (statement fidelity).** The FALSE format quantifies over an
arbitrary magma, so it admits infinite carriers; what is narrower is only the
*mechanical finite shape* (`Fin n` table + `decideFin!`). An infinite
counterexample is certifiable, but requires a genuine Lean proof of the
hypothesis and the refutation rather than a decidable table. It is recorded
because two public instances (§7) lie outside both our finite search and
EULER's proof-supported infinite recognizer, and because no downstream
verification can detect a problem/statement mismatch — the central claim of
the accompanying paper,
and twice observed empirically in this project's own tooling
(`4-STATEMENT-FIDELITY.md`, failures A and B).

## 2. The direction relation

**Claim 2.1.** Let R ⊆ [4694]² be the embedded bitmatrix. R coincides with
the ETP-computed implication relation on the order-4 law catalog:
the blob is byte-identical to the public `outcomes.json` closure, and an
independent recomputation produced zero disagreements.
*Status:* computationally verified (deterministic data comparison).
*Trusted base:* the ETP computation (public, independently re-runnable) and
a byte-level diff.

**Claim 2.2.** On the three order-4 official evaluation subsets (600
problems), the verdict read from R agrees with the organizers' published
answers in 600 cases out of 600.
*Status:* computationally verified (lookup vs published ground truth).

R is used only to *select a branch*; no submitted answer depends on R for
its validity, since every answer carries its own certificate (§4).

## 3. FALSE certificates

**Proposition 3.1.** If (Fin n, t) ⊨ E1 and (Fin n, t) ⊭ E2, then
E1 ⊭ E2. □ (Immediate: a countermodel.)

**Claim 3.2 (pre-emission check).** The solver emits (n, t) only after
exhaustively evaluating both laws over all |V₁|- and |V₂|-tuples of Fin n —
the same finite semantics the judge re-decides. No sampling. Across every
measurement in this pack, the count of emitted-but-invalid witnesses is 0.
*Status:* computationally verified per emission; the judge re-establishes
it per answer.

**Claim 3.3 (held-out generalization).** On 120 order-4 FALSE instances
excluded from every released problem set, and on 100 instances whose
hypothesis law appears in no released set, the bank-plus-search pipeline
produced valid witnesses in 120/120 and 100/100 cases. Reproducible: the
seeded generator and immutable cohort manifests are in `evidence/held-out-cohorts/`
(`reproduce_heldout.py`, `RESULTS.md`); both cohorts are held out from every
released set by construction.
*Status:* computationally verified. This — not the released-set sweep,
which the harvest targeted (§7) — is the generalization claim of record.

## 4. TRUE certificates and the soundness invariant

**Theorem 4.1 (no unverified accept).** No answer counts unless the
deterministic Lean judge accepts it. Every deterministic-tier answer
additionally passes an independent check before submission; the grind and LLM
tiers pass no prior check and reach the judge as unverified guesses, gated
solely by its acceptance.
*Proof sketch (structural, by cases on emit paths).* (i) FALSE emissions:
Claim 3.2's exhaustive evaluation. (ii) Certificate-table entries (26
manual, 390 Aristotle-proved, 18 ATP/loop): literal Lean bodies,
kernel-checked at creation on the judge's exact toolchain, re-checked by
the judge at answer time. (iii) Chain proofs: each rewrite step is re-walked
against the rule set before emission. (iv) Completion proofs: the emitter
is total — the emission templates are correct-by-construction, so validity
of an emitted body is a property of the emitter, established by audit
(seeded-random suites, 0 invalid emissions post-fix) rather than assumed.
(v) Transitivity compositions: `have`-chaining of hop proofs each of which
is itself an item (iii)/(iv) artifact. (vi) LLM-tier candidates: no
intrinsic check — this path exists *only* behind the judge gate and cannot
finalize without `accepted`. In the Marathon track (no runtime judge),
paths (iii)–(v) alone may write. There is no other emit path; inspection of
`solve()` confirms the case analysis is exhaustive. □

**Remark.** Theorem 4.1 is a statement about program structure, verified by
audit of the emit sites, not a formal proof about the program text. The
judge's per-answer check is what converts it into a guarantee per submitted
answer.

## 5. The collapse theorem

The pivotal instance, stated and proved precisely.

**Notation.** E₁₆₈₉: ∀ x y z. x = (y ◇ x) ◇ ((x ◇ z) ◇ z).
E₂₃₉₁: ∀ x y z. x = (y ◇ (z ◇ (y ◇ z))) ◇ z.

**Theorem 5.1.** Every magma satisfying E₁₆₈₉ has at most one element.
Consequently E₁₆₈₉ ⊨ E for *every* equational law E; in particular
E₁₆₈₉ ⊨ E₂₃₉₁.

**Proof.** Work in an arbitrary (G, ◇) ⊨ E₁₆₈₉; write h for the hypothesis.
The kernel-checked certificate (artifact: `8-TRACE/final2_solved.json`;
compiles under Lean v4.32.2 against the judge goal) derives a ladder of
consequences L1–L10 of h by explicit equational steps; the two that carry
the argument:

  L6 : ∀ a b. a ◇ ((a ◇ b) ◇ b) = a
  L10: ∀ a b. a = a ◇ b

L10's derivation, verbatim from the certificate (a three-step calc from L6,
an idempotent-collapse lemma L8, and h itself):

```lean
have L10 : ∀ (x1 x0 : G), x1 = (x1 ◇ x0) := by
  intro x1 x0
  calc x1
    _ = (x1 ◇ ((x1 ◇ x0) ◇ x0)) := (L6 x1 x0).symm
    _ = (x1 ◇ ((x1 ◇ x0) ◇ ((x0 ◇ ((x0 ◇ x1) ◇ x1)) ◇ ((x0 ◇ x1) ◇ x1))))
        := congrArg (fun t => (x1 ◇ ((x1 ◇ x0) ◇ t))) (L8 x0 x1).symm
    _ = (x1 ◇ x0)
        := congrArg (fun t => (x1 ◇ t)) (h x0 x1 ((x0 ◇ x1) ◇ x1)).symm
```

From h and L10, total collapse — the step no rewrite system produces,
because it is not a rewrite:

```lean
have ALLEQ : ∀ (a b : G), a = b := by
  intro a b
  have s1 : a = b ◇ a :=
    (h a b a).trans ((L10 (b ◇ a) ((a ◇ a) ◇ a))).symm
  exact s1.trans ((L10 b a)).symm
```

In words: h at (a, b, a) gives a = (b ◇ a) ◇ ((a ◇ a) ◇ a); L10
instantiated at (b ◇ a) and ((a ◇ a) ◇ a), reversed, contracts the right
side to b ◇ a; hence a = b ◇ a. L10 at (b, a), reversed, gives b ◇ a = b.
By transitivity a = b for all a, b — G is a subsingleton.

For the consequence: let E be any law ∀V. s = t. Under any assignment into
a subsingleton G, s and t denote elements of G, hence are equal (for empty
G the quantification is vacuous). So (G, ◇) ⊨ E. The goal E₂₃₉₁ is the
instance `exact ALLEQ x ((y ◇ (z ◇ (y ◇ z))) ◇ z)`. □

*Status:* the full certificate, including the L1–L9 bodies elided here, is
kernel-checked on the judge's exact toolchain; the surrounding argument in
this section is human prose over kernel-checked steps.
*Provenance:* L1–L10 were discovered by bounded Knuth–Bendix completion;
the ALLEQ construction is a human step; the certificate does not
distinguish these origins, and the kernel did not need to.

## 6. Verification statuses (badge semantics, precise)

For every reported figure, the pair (what was checked, trusted base):

- **Computationally verified** — exhaustive finite evaluation or
  deterministic comparison; trusted base: a ~30-line evaluator itself
  cross-validated against judge acceptance on hundreds of certificates.
- **Verified (judge-toolchain)** — the exact artifact compiles and closes
  its stated goal on Lean v4.32.2 (`f3b06c705…`) against the judge-faithful
  goal wrapper; trusted base: the Lean kernel and the wrapper's fidelity,
  the latter itself rebuilt from the judge's published source after
  fidelity failure A and therefore not self-certified.
- **Ceiling** — composed of verified parts, not the product of an official
  end-to-end judge run. The released-set 800/800 carries this badge and, in
  addition, leans on pair-keyed certificates for released instances.
- **Official** — organizer's judge verdict in production. *No artifact in
  this pack carries this badge.* One production run effects the conversion;
  this sentence is reproduced wherever a figure appears.

## 7. What is not established

1. **No private-set performance claim is made.** The organizers state
   released evaluation instances will not recur privately; the pair-keyed
   certificate layers are therefore regression coverage only. What is
   offered for the private set: the generalizing tiers and Claim 3.3.
2. **Two public FALSE instances are unresolved**: 1167 ⇒ 1763 (no
   countermodel through order 8, search exhausted) and 2531 ⇒ 4307 (orders
   2–6 exhausted; order 7 terminated on budget). Non-existence of finite
   countermodels is *not* claimed; if either implication fails only in
   infinite magmas, it needs a proof-supported infinite certificate rather
   than a finite table (§1, Remark) — permitted by the format but not reached
   by our finite search or the parity recognizer.
3. **The runtime 3-hop transitivity tier is strictly weaker than the
   dev-time search that motivated it** (its forward frontier is drawn from
   the 2-hop candidate list rather than all successors); recorded as a
   known limitation.
4. **Theorem 4.1 is an audited structural property, not a machine-checked
   theorem about the program.** The judge's per-answer verification is the
   load-bearing guarantee.

## 8. Artifacts

Solver: `2-SOLVER/solver.py`, 442,061 bytes, SHA-256
`e0f7ac8406f48c3054bea202cb1fbac1fb4988d6643551d2e9617d62c9b48329`.
Certificates and contemporaneous trace: `8-TRACE/`. Fidelity record:
`4-STATEMENT-FIDELITY.md`. Provenance ledger and re-derivation recipe:
`7-TRUST/`. External systems (dev-time only; every output independently
re-verified): ETP public data (Tao et al.); Axle (Axiom — judge-toolchain
compile checks; the discovery instrument for both fidelity failures);
Aristotle (Harmonic — the 390 table proofs); Vampire, E, Mace4. The
competition's judge, harness, and goal construction: SAIR Foundation, open
repository.

Everything above either cites a checkable artifact or names the check it
awaits. That is the standard the criterion asks for, and it is the standard
this account was written to meet.
