# EULER: A Certificate-Emitting Solver for Equational Implication, Packaged to a Reactivation Standard

**Christopher Brock**
Riemann Labs
`chrisbrock54@gmail.com`

*Draft — 2026-08-25. Companion to "Mathematics in the Age of Mechanical
Reproduction" (Brock, 2026). Prepared for the SAIR Mathematics Distillation
Challenge, Equational Theories, Stage 2.*

---

## Abstract

We describe EULER, a solver for the equational-implication problem over magmas
posed by the SAIR Mathematics Distillation Challenge, Stage 2. Given two
single-axiom identities `E1`, `E2` over one binary operation, EULER decides
whether every magma satisfying `E1` satisfies `E2`, and emits a
machine-checkable certificate — a finite countermodel for FALSE, a Lean 4 proof
for TRUE — re-verified by the competition's open, deterministic judge. The
solver is organized as a *refusal stack*: direction is read from a precomputed
public implication closure rather than guessed; no answer counts unless the
judge accepts it, and the deterministic tiers additionally self-check before
emitting; and no single proof method is trusted to cover the space. We report, with explicit verification badges, an exact
direction agreement of 600/600 against the organizers' published answers, a
held-out FALSE generalization of 120/120 (and 100/100 on novel hypotheses), and
a released-set solve ceiling of 800/800 which we mark as a *ceiling* because it
leans on pair-keyed certificates for released problems that the organizers state
will not recur privately. The contribution is as much methodological as
technical: the solver is submitted inside a package built to the standard of its
accompanying paper — a statement-fidelity record (including two fidelity failures
we caught in our own tooling), a reactivation packet separating contemporaneous
evidence from retrospective rationale, and per-artifact epistemic badges. We
argue this packaging is not ornamental but a response to a real gap that formal
verification alone does not close.

---

## 1. The problem, and why it is an unusual setting

A **magma** is a set `G` with one binary operation `◇ : G × G → G` and no axioms.
An **equational law** is a universally quantified identity in `◇` — for example
law 1689 of the Equational Theories Project catalog,

> `∀ x y z. x = (y ◇ x) ◇ ((x ◇ z) ◇ z)`.

The Stage-2 decision problem takes an ordered pair `(E1, E2)` and asks whether
`E1 ⊨ E2`: does every magma satisfying `E1` satisfy `E2`? By Birkhoff's
completeness theorem for equational logic, semantic implication over the class of
all magmas coincides with derivability in the equational calculus, so we move
freely between the two readings.

The competition fixes the certificate formats and the trusted base. A **FALSE**
answer exhibits `n` and a table `t : Fin n × Fin n → Fin n` with
`(Fin n, t) ⊨ E1` and `(Fin n, t) ⊭ E2`; the judge re-decides both finite claims
via `decideFin!`. A **TRUE** answer is a Lean 4 term of the goal type
`∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G`, kernel-checked under Lean
v4.32.2 (pinned commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`), with axioms
restricted to `{propext, Quot.sound, Classical.choice}` and the `sorry` family,
metaprogramming, and unsafe primitives rejected by token and dependency-closure
audit. The sandbox is a bare `python:3.11-slim` container — 2 vCPU, 2 GB, no
network, one source file at most 500 KB, 3600 s per problem. There is no partial
credit; the judge's verdict is the only score.

This setting is unusual, and the unusualness is the point. Verification is *free
and perfect*: the judge will not accept an invalid proof, and it costs the solver
nothing to be checked. That moves all of the interest onto the questions
verification does not answer — how correct certificates are *produced* at scale,
which method to trust for which problem, and how to report what has and has not
been established. These are exactly the questions the companion paper argues have
become the load-bearing epistemics of machine mathematics.

## 2. Architecture: a refusal stack

EULER is built from three refusals, each of which is also a design principle.

**Refusal I — do not guess what is known.** For the 4,694 laws of the catalog's
order-4 core, the Equational Theories Project (Tao et al.) has computed and
published the complete pairwise implication closure. EULER embeds this closure as
a 4,694² bitmatrix (≈110 KB compressed), byte-identical to the public
`outcomes.json` and recomputed with zero disagreements. On any order-4 pair the
direction is therefore *exact*, read in constant time. §5 reports the validation:
600/600 against the organizers' own evaluation answers. For contrast, the public
Stage-1 benchmark records the best of twenty-five large language models at 69%
direction accuracy on hard instances, most at the base rate. The design
conclusion is not an argument against models; it is arithmetic. The embedded
matrix only *selects a branch* — no submitted answer depends on it for validity,
because every answer carries its own independently-checked certificate.

**Refusal II — do not trust cleverness.** No answer counts unless the judge
accepts it; the deterministic tiers additionally pass an independent check before
emitting. FALSE tables are exhaustively evaluated against both laws (no sampling)
in `decideFin!` semantics; TRUE chains are re-walked step by step; completion
proofs are emitted by a *total* emitter (§3.2). The grind and LLM tiers pass no
prior check and reach the judge as unverified guesses — gated solely by its
acceptance. The central structural claim (Theorem 4.1) is that there is no code
path from heuristic confidence to a *judge-accepted* answer.

**Refusal III — do not stop at one method.** The FALSE and TRUE sides are each a
cheapest-first cascade of independent techniques, detailed next.

### 2.1 FALSE side: promiscuous finite witnesses

A single finite magma satisfies a large family of laws, so a modest library of
tables, *keyed by which hypothesis each satisfies*, refutes far more implications
than it was built from. EULER embeds a bank of 305 finite magmas (orders 2–9);
at answer time it scans for a table satisfying `E1` and refuting `E2`. When the
bank misses, a pure-stdlib backtracking finite-model finder (orders 4–8, forward
checking, restricted-growth symmetry breaking) searches for a new witness. Every
emitted table is exhaustively self-checked before the judge sees it; the count of
emitted-but-invalid witnesses is zero across all measurements. The bank's
generalization — not its released-set coverage — is the claim of record (§5).

### 2.2 TRUE side: a technique ladder

Given TRUE direction, EULER climbs a ladder, cheapest first:

1. **Certificate table** — 26 hand-derived proofs, 390 proved dev-time by
   Harmonic's Aristotle prover, and 18 derived by classical ATPs or the
   improvement loop (§6); all are literal Lean bodies, all disclosed, all
   re-verified by the judge at answer time.
2. **Matching-chain prover** — treats `E1` as a bidirectional rewrite rule and
   searches for a chain from one side of `E2` to the other, re-walking every step
   before emitting a Lean `calc`.
3. **Bounded Knuth–Bendix completion** — an embedded, pure-stdlib engine that
   derives critical-pair consequences of `E1`, detects projection/collapse laws,
   and emits explicit `have`-ladders. §3 discusses its two load-bearing
   properties.
4. **Transitivity** — factors a hard `i ⇒ j` through provable intermediate laws.
   The tier is licensed by a recomputed fact: the closure of the 10,657 public
   `explicit_proof_true` edges equals all 8,178,279 order-4 TRUE pairs exactly
   (missing 0, extra 0). EULER composes two-hop, then a bounded three-hop
   meet-in-the-middle.
5. **ATP replay** — reconstructs an E-prover superposition proof node-by-node
   into named Lean `have`s (shared-DAG, common subproofs emitted once), turning
   the prover's own derivation into a human-checkable artifact.
6. A judge-gated LLM fallback, never reached on the order-4 core.

## 3. Two properties that make the completion tier safe

The completion engine (a compact reimplementation in the Twee/Knuth–Bendix
lineage) carries the technique ladder's hardest cases, and two engineering
properties matter more than its raw power.

### 3.1 Termination

An early version did not terminate on some inputs. The cause: a rewrite rule
could match a subterm with permuted variables, producing a cyclic match
substitution `{a ↦ b, b ↦ a}` and an infinite walk. The fix is a one-pass
simultaneous substitution (`subst_flat`), equal to ordinary application when
there is no collision and always terminating; a hard per-problem deadline
backstops it. Measured on a 90-pair stress suite: zero hangs.

### 3.2 Total emission

The completion tier's soundness does not rest on the judge, because in the
Marathon track (§4) there is no judge at runtime. Instead the emitter is
**total**: if it emits a proof body, that body is valid Lean. This is achieved by
making the emission templates correct-by-construction — the const-collapse
template, in particular, was re-derived after a seeded-random audit surfaced 18
invalid emissions, and re-tested to zero invalid emissions on unseen seeds. A
prover whose *output* is trustworthy, independent of any external check, is a
different object from one that merely proposes candidates; only the former may
write in a judge-free track.

## 4. Soundness

**Theorem 4.1 (no unverified exit).** Every answer EULER submits has passed an
independent validity check prior to submission, and is checked again by the
judge.

*Proof (structural, by cases on emit paths).* (i) FALSE emissions: the exhaustive
finite evaluation of §2.1. (ii) Certificate-table entries: literal Lean bodies,
kernel-checked at creation on the judge's toolchain, re-checked by the judge.
(iii) Chain proofs: each rewrite step re-walked before emission. (iv) Completion
proofs: total emission (§3.2), a property of the emitter, established by audit
rather than assumed. (v) Transitivity: `have`-chaining of hop proofs each of
which is an (iii)/(iv) artifact. (vi) LLM candidates: no intrinsic check, hence
reachable only behind the judge gate, which cannot finalize without `accepted`.
In the Marathon track only paths (iii)–(v) may write. Inspection of the emit
sites confirms the case analysis is exhaustive. ∎

*Remark.* Theorem 4.1 is an audited structural property of the program, not a
machine-checked theorem about the program text; the judge's per-answer check is
the load-bearing guarantee, and Theorem 4.1 explains why the solver never *needs*
it to reject.

**Robustness.** The live judge was once observed returning an infrastructure
error (an incompatible `Magma.olean` header — a toolchain mismatch on the
organizers' side, not a solver defect). EULER carries a fail-fast: on detecting
such a marker it short-circuits all subsequent judge calls, so a broken judge
costs seconds rather than the full budget.

## 5. The collapse: a case study in search versus insight

One instance locates the boundary between mechanical search and human insight
with unusual clarity, and we give it in full because it is the clearest single
demonstration of the division of labor this paper is about.

**Theorem 5.1.** Every magma satisfying `E1689` has at most one element.
Consequently `E1689 ⊨ E` for every equational law `E`; in particular
`E1689 ⊨ E2391`, where

> `E1689 : ∀ x y z. x = (y ◇ x) ◇ ((x ◇ z) ◇ z)`,
> `E2391 : ∀ x y z. x = (y ◇ (z ◇ (y ◇ z))) ◇ z`.

Every search tier of §2.2 failed on this pair, and correctly so: chain search
saturated because the goal is *not reachable* by rewriting; deep chain at depth
10 / 1500 s saturated in seconds; two-hop transitivity starved on a measurable
bottleneck — the forward provable-edge frontier ranged 1–7 against backward
frontiers of 27–60, so first-edge provability, not path existence, was the
constraint. The completion engine, however, had derived a projection law.

*Proof of 5.1.* Work in an arbitrary `(G, ◇) ⊨ E1689`; write `h` for the
hypothesis. The kernel-checked certificate derives a ladder `L1…L10` of
consequences of `h`; the two that carry the argument are

> `L6 : ∀ a b. a ◇ ((a ◇ b) ◇ b) = a`,
> `L10 : ∀ a b. a = a ◇ b`.

`L10`'s derivation, verbatim from the certificate — a three-step `calc` through
`L6`, an idempotent-collapse lemma `L8`, and `h` itself:

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

From `h` and `L10`, total collapse — the step no rewrite system produces,
because it is not a rewrite:

```lean
have ALLEQ : ∀ (a b : G), a = b := by
  intro a b
  have s1 : a = b ◇ a :=
    (h a b a).trans ((L10 (b ◇ a) ((a ◇ a) ◇ a))).symm
  exact s1.trans ((L10 b a)).symm
```

That is: `h` at `(a, b, a)` gives `a = (b ◇ a) ◇ ((a ◇ a) ◇ a)`; `L10`,
instantiated at `(b ◇ a)` and `((a ◇ a) ◇ a)` and reversed, contracts the right
side to `b ◇ a`, so `a = b ◇ a`; `L10` at `(b, a)` reversed gives `b ◇ a = b`;
transitivity yields `a = b`. Hence `G` is a subsingleton. Under any assignment
into a subsingleton, both sides of any law denote elements of `G` and are equal
(for empty `G`, vacuously). The goal `E2391` is the instance
`exact ALLEQ x ((y ◇ (z ◇ (y ◇ z))) ◇ z)`. ∎

The lesson generalizes past this pair. Rewriting proves *reachability*; collapse
is a statement about the *model class*, and crossing that categorical line is not
a rewrite step. The completion engine had derived `L10` — the decisive fact was
in the machine's hands — and still could not finish, because its language of
thought cannot express "all elements are equal." Seeing *what kind of statement*
the goal is took a human act; writing it down took three lines; and the kernel
checked those lines against the axioms without regard for who wrote them. The
division of labor was not human *or* machine: machine searches, human sees, judge
disposes.

## 6. Measurement, with verification badges

We separate every reported figure from its verification status, using four
badges. **Computationally verified** — exhaustive finite evaluation or
deterministic comparison, trusted base a small evaluator itself cross-validated
against judge acceptance on hundreds of certificates. **Verified
(judge-toolchain)** — the exact artifact compiles and closes its goal on Lean
v4.32.2 against a judge-faithful goal wrapper. **Ceiling** — composed of verified
parts but not the product of an official end-to-end judge run. **Official** — an
organizer judge verdict in production; *no artifact in this work carries this
badge.*

| Claim | Value | Badge |
|---|---|---|
| Direction vs official answers, order-4 evaluation sets | **600 / 600** | Computationally verified |
| Held-out FALSE — pairs absent from every released set | **120 / 120** | Computationally verified |

The held-out cohorts are reproducible: `HELD-OUT-COHORTS/reproduce_heldout.py` regenerates both (seeded, held out from every released set by construction) with an immutable result log; 0 invalid witnesses.
| Held-out FALSE — novel hypotheses (never in any released set) | **100 / 100** | Computationally verified |
| Released evaluation sets (4 × 200) | **800 / 800** | Ceiling |
| Order-5 evaluation set (fully outside the oracle) | **190 / 200** organic | Computationally verified |
| Official judge run | — | *none yet* |

Two inflation risks were found and controlled *by us*, not surfaced by a referee,
and we name them because unnamed they would silently inflate the headline. First,
the FALSE bank's Mace4 harvest *targeted* the released evaluation sets; the
released-set FALSE coverage is therefore inflated by construction, and the
held-out numbers above — not the released-set figure — are the generalization
claim of record. Second, the released-set 800/800 leans on pair-keyed
certificates for released TRUE rows (the certificate table of §2.2); these are
disclosed per pair and are *regression coverage only*, since the organizers state
released rows will not recur in the private set. What is offered for the private
set is the set of generalizing tiers — the hypothesis-keyed bank, the runtime
model finder, chain and completion proving, transitivity — together with the
held-out FALSE evidence.

The last attempted official run (2026-08-20) failed on the organizers'
infrastructure error noted in §4; it is documented and reported, and counted as
evidence in neither direction. One production judge run converts every ceiling in
the table above to an official result.

## 7. The field: two philosophies, one judge

The public Stage-2 field has divided into two design philosophies, and the
division is worth stating because it clarifies what EULER is. One school lets a
language model *steer* mechanically-verified tools: the model proposes lemma
bridges and model searches, which are treated as untrusted hints and
mechanically proven before use — a genuinely sound design, hostage to a weak
proxy model and blind on direction. EULER is the other school: it precomputes the
mathematics — an exact direction oracle from public data, deterministic provers,
disclosed certificates. Both are sound; both terminate at the same deterministic
judge. The difference is reproducibility. EULER's every result can be regenerated
*without any model in the loop*, from public materials, on a laptop. That is not
a competitive tactic. It is the companion paper's thesis — that a discipline
losing the capacity to reactivate its deposits may retain every result while
losing what made it knowledge — instantiated, with a live empirical contrast in
the same competition.

## 8. Reproducibility and provenance

The design was not chosen; it was forced, in order, by measurements anyone can
repeat: (1) the public ETP closure decides direction exactly, and the public LLM
benchmark shows models cannot — so direction is embedded, not guessed; (2) a
FALSE answer is a finite magma, so generate structured families, run any
finite-model finder offline, re-verify each witness, embed the literal tables;
(3) many TRUE implications are rewrite chains — implement and self-recheck them;
(4) constancy/collapse laws are not reachable by rewriting but are consequences
of completion — implement bounded Knuth–Bendix with total emission; (5) the
residue factors through intermediate laws, licensed by a closure computation on
public data; (6) verify everything against the judge's exact toolchain, the judge
being the arbiter, not the developer. The tools required are the public ETP
repository, any finite-model finder, any Lean v4.32.2 environment, and the public
SAIR Stage-2 harness. No proprietary data; hours of laptop compute, not
GPU-scale.

Every embedded payload is disclosed and traceable. The direction matrix and the
equation texts are public ETP data, diffable against upstream. The 305-magma bank
is literal tables, each finitely re-checkable. The 390 Layer-1 proofs were
produced dev-time by **Aristotle** (Harmonic's Lean theorem prover) and are
re-verified by the judge at answer time. The pair-keyed loop certificates were
produced by the classical stack — **Vampire** (Kovács & Voronkov), **E**
(Schulz), **Mace4** (McCune) — and reconstructed into human-checkable Lean.
Every one of these certificates was compile-checked during development on the
judge's exact toolchain by **Axle**, Axiom's cloud Lean verification engine
(Carina Hong and the Axiom Math team); Axle's ~2-second checks, against a
~40-minute playground round trip, made the project's measurement discipline
practical, and both statement-fidelity failures reported below were *discovered*
as Axle divergences. None of these systems is a runtime dependency; all shaped
what the runtime carries; and everything any of them produced was re-verified at
least twice before the judge saw it.

## 9. Statement fidelity, and what verification cannot do

Formal verification adjudicates the relation between a formal statement and its
proof. It is silent on the relation between that statement and the informal
problem it was meant to express — the unguarded arrow the companion paper names.
We record two failures from our own tooling, because they are the clearest
evidence that the layer is real, and because a checker can be flawless while the
statement it checks is not the statement intended.

*Failure A.* A dev-time verifier constructed its own version of the goal whose
variable-binding convention differed subtly from the judge's; it *accepted*
proofs the real judge rejected — verified against the wrong statement. Remedy: the
goal wrapper was rebuilt from the judge's published source, and every
"verified" claim in this work postdates that rebuild.

*Failure B.* The evaluation files write the operation as `*`; our verification
wrapper interpolated equation text into a Lean preamble defining only `◇`, so
Lean demanded a nonexistent `Mul` instance and *rejected* five mathematically
correct proofs. For one measurement cycle the record read 0/7 where the truth was
5/7. Remedy: operator normalization at the wrapper boundary.

Both failures were in the *statement rendering*, not the mathematics, and the
proof checker was working perfectly through both. They are the empirical form of
the claim that no procedure operating solely on a target proposition and its
proof can certify fidelity to a prior informal intention.

## 10. Limitations

We state plainly what is not established. (1) No private-set performance figure is
offered; the pair-keyed certificate layers are regression coverage only. (2) Two
public FALSE pairs are unresolved — `1167 ⇒ 1763` (no finite countermodel through
order 8) and `2531 ⇒ 4307` (orders 2–6 exhausted, order 7 terminated on budget);
we do not claim no finite countermodel exists, and an implication refutable only
by infinite magmas lies outside the competition's finite FALSE format. (3) The
runtime three-hop transitivity tier is strictly weaker than the dev-time search
that motivated it — its forward frontier is drawn from the two-hop candidate list
rather than all successors — recorded as a known limitation. (4) Theorem 4.1 is
audited, not machine-checked; the judge's per-answer verification is the
guarantee. (5) All figures in §6 are ceilings on the judge's exact toolchain, not
official runs.

## 11. Conclusion

EULER is a small system that decides equational implications and proves its
answers, and its technical core — an exact direction oracle, a hypothesis-keyed
countermodel bank, a completion engine with total emission, transitivity
composition, and ATP replay, all behind an independent-check invariant — is
strong on the released material and honest about the boundary of what it
establishes. But the argument of this paper is that the technical core is only
half of a Stage-2 submission worth making under Tao's criterion. The other half
is reactivation: the certificates, the failure history that produced them, the
fidelity decisions beneath them, and the verification status of every claim,
shipped as first-class artifacts, so that a competent reader — not just the
kernel — can recover the sense that makes the result knowledge. We built the
solver to answer the questions. We packaged it to answer the harder one.

---

## References

- E. Husserl, *The Crisis of European Sciences and Transcendental
  Phenomenology*, 1936 (incl. "The Origin of Geometry").
- W. Benjamin, "The Work of Art in the Age of Mechanical Reproduction," 1936.
- A. M. Turing, "On Computable Numbers," *Proc. LMS*, 1937; "Systems of Logic
  Based on Ordinals," 1939.
- A. Jaffe and F. Quinn, "'Theoretical Mathematics'," *Bull. AMS* 29 (1993).
- W. P. Thurston, "On Proof and Progress in Mathematics," *Bull. AMS* 30 (1994).
- D. Knuth and P. Bendix, "Simple Word Problems in Universal Algebras," 1970.
- N. Smallbone, Twee (equational theorem prover).
- W. McCune, Mace4 (finite model finder).
- S. Schulz, E (theorem prover). L. Kovács and A. Voronkov, Vampire.
- T. Tao et al., *The Equational Theories Project*,
  `github.com/teorth/equational_theories`.
- T. Tao, *Mathematics in the Age of AI*, ICM, 2026.
- T. Klowden and T. Tao, "Mathematical methods and human thought in the age of
  AI," 2026.
- *The Leiden Declaration on Artificial Intelligence and Mathematics*, 2026.
- C. Brock, *Mathematics in the Age of Mechanical Reproduction*, 2026 (companion).
- SAIR Foundation, *Mathematics Distillation Challenge — Equational Theories,
  Stage 2*, open judge repository.

## Artifacts

Solver of record: `solver.py`, 442,061 bytes, SHA-256
`e0f7ac8406f48c3054bea202cb1fbac1fb4988d6643551d2e9617d62c9b48329`, one file,
both tracks. Contribution pack (this document's parent): embedded-data
disclosure, reactivation packet, statement-fidelity record, epistemic-badge
table, workflow diagrams, four graded expositions, and the contemporaneous
process-evidence trace. Every load-bearing claim herein either cites a checkable
artifact or names the check it awaits.
