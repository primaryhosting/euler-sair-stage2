# EULER, Explained
## An expert-level exposition of a certificate-emitting solver for equational implication
*(This document is the pack's demonstration artifact — per the paper's
"make the demonstration the artifact": a recorded, publicly postable,
expert-level exposition, checkable by anyone competent, requiring no room
to be opened. It is written to be delivered as a talk. Attribution is given
at every point where an idea is not ours.)*

---

## 1. The problem

A **magma** is a set with one binary operation `◇` and no axioms. An
equational law is a universally quantified identity, e.g. law 1689:

> ∀ x y z:  x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

The task (SAIR Mathematics Distillation Challenge, Stage 2, an outgrowth of
the Equational Theories Project of Tao and collaborators): given laws E1,
E2, decide whether **every** magma satisfying E1 satisfies E2 — and prove
your answer in Lean 4, machine-checked by a deterministic judge. FALSE means
exhibiting a finite operation table; TRUE means a kernel-checked implication
proof. No partial credit; the judge's verdict is the only score.

This is an adversarial setting for the "solve, verify, and it's done"
picture: the verifier is perfect, the statement is fixed by the organizers,
and everything interesting lives in *how* correct certificates get produced
at scale — which is exactly where the accompanying paper argues the
epistemics now live.

## 2. Six ideas, in the order the evidence forced them

**Idea 1 — Direction is a table, not a question.** The ETP already computed
the full implication closure for all 4694 order-4 laws (Tao et al.,
`outcomes.json`). Embedded as a 4694² bitmatrix, it answers TRUE/FALSE
*exactly*: 600/600 against the competition's published evaluation answers.
For contrast, on the competition's own public benchmark the best of 25
language models reaches 69% direction accuracy on hard instances; most sit
at the base rate. The design conclusion is not anti-model ideology — it is
arithmetic.

**Idea 2 — Finite magmas are promiscuous witnesses.** One operation table
satisfies a large family of laws. So a bank of ~300 tables, indexed by which
*hypotheses* each satisfies, refutes vastly more implications than it was
built from. Measured on pairs held out from every released problem set:
120/120; on pairs whose hypothesis never appears in any released set:
100/100. When the bank misses, a pure-stdlib backtracking search over the
n×n table (forward checking, symmetry breaking — the Mace4/Paradox lineage,
after McCune) finds novel witnesses at orders 4–8. Every witness is checked
against both laws by full finite evaluation before emission, and the judge's
`decideFin!` re-proves it in Lean.

**Idea 3 — Most TRUE implications are rewrite chains.** Treat E1 as a
rewrite rule (both directions, at any subterm, with unification); search for
a chain from one side of E2 to the other; re-walk the chain step-by-step
before emitting it as a Lean `calc`. (The chain technique follows the
public Stage-2 leader's approach, independently reimplemented; the
reconstruction style is related to Krympa, Kondylidou et al.)

**Idea 4 — When rewriting saturates, complete.** Constancy and collapse
laws defeat chain search: the goal is not *reachable* by rewriting, it is a
*consequence* of the theory's completion. A bounded Knuth–Bendix engine
(after Knuth–Bendix 1970; scale demonstrated by Smallbone's Twee) derives
critical-pair lemmas and emits explicit `have`-chains. Two engineering
properties matter more than power: emission is **total** (if it emits, the
Lean is valid — the const-collapse template is correct-by-construction) and
**terminating** (hard deadline; a substitution-cycle infinite loop was found
and fixed). Total emission is what makes this tier safe in the Marathon
track, where there is no judge at runtime.

**Idea 5 — The residue factors.** What survives all direct provers falls to
three factorings: through an **intermediate law** (if `i ⇒ k` and `k ⇒ j`
are each directly provable, compose the proofs — licensed by a recomputed
fact: the closure of the 10,657 public explicit-proof edges is exactly the
8,178,279 order-4 TRUE pairs); through a **collapse lemma** (worked in full
in §3); or through an **ATP's own derivation, replayed** — E's superposition
proof reconstructed node-by-node into named Lean `have`s, so the machine's
proof becomes a human-checkable one (E: Schulz; Vampire: Kovács & Voronkov).

**Idea 6 — The author never certifies his own work.** Every emit path ends
at an independent check — full finite evaluation, chain re-walk, total
emission, or the Lean kernel — and in the Solo track the competition judge
gates every single answer. The solver cannot submit an unverified guess;
there is no code path for it.

## 3. One pivotal proof, worked in full

*(the paper's reactivation test asks for exactly this: explain an
arbitrarily chosen pivotal step. We choose the one that best shows why
rewriting alone cannot finish, and how little is needed once you see it.)*

**Problem:** law 1689 ⇒ law 2391. Hypothesis and goal:

    h    : ∀ x y z,  x = (y ◇ x) ◇ ((x ◇ z) ◇ z)
    goal : ∀ x y z,  x = (y ◇ (z ◇ (y ◇ z))) ◇ z

Chain search fails here at every budget — and *should*: we will show the
hypothesis forces the magma to collapse to a point, and "everything equals
everything" is not reachable by rewriting one side of the goal into the
other. It must be constructed.

**Step 1 (completion finds the lever).** Knuth–Bendix completion on `h`
derives, among its critical-pair lemmas, a projection law:

    L10 : ∀ a b,  a = a ◇ b

(Each derivation step is an explicit two- or three-step rewrite chain from
`h`; the emitted Lean carries all of them as `have`-blocks — nothing is
asserted, everything is derived.)

**Step 2 (the construction rewriting cannot make).** From `h` and `L10`,
total collapse, in three lines:

    Instantiate h at (a, b, a):    a = (b ◇ a) ◇ ((a ◇ a) ◇ a)
    Instantiate L10 at (b ◇ a) and ((a ◇ a) ◇ a):
                                   b ◇ a = (b ◇ a) ◇ ((a ◇ a) ◇ a)
    Chain the two (trans/symm):    a = b ◇ a
    Instantiate L10 at (b, a):     b = b ◇ a
    Chain again:                   a = b                          ∎

So:  **ALLEQ : ∀ a b, a = b.**  In Lean this is four `have`s and two
`.trans`-compositions — kernel-checked equality reasoning, no tactics beyond
`intro`/`exact`.

**Step 3 (the goal evaporates).** Any equation between any two terms is now
an instance:

    exact ALLEQ x ((y ◇ (z ◇ (y ◇ z))) ◇ z)

The full certificate (completion scaffold + ALLEQ + one `exact`, 3,927
bytes) compiles under the judge's exact toolchain, Lean v4.32.2.

**Why this step is pivotal:** it is the cleanest boundary in the whole
solver between *search* and *insight*. The completion engine had already
derived `L10` — the machine had the lever in hand — and still could not
finish, because its proof language (rewriting) cannot express "now conclude
all elements are equal." One human observation about *what kind of statement
the goal is* turned an unsolvable problem into three lines. That division of
labor, stated honestly, is the paper's subject.

## 4. What failed, and what the failures taught

*(compressed from the reactivation packet, which carries the dated record)*

- **LLM direction** (69% best) → direction moved to the embedded closure.
- **LLM proving** (0/6 on structural TRUEs; ATPs 6/6 in milliseconds) →
  deterministic proving stack.
- **Two-hop transitivity** failed on eight problems for a measurable reason:
  the *first-edge* provable frontier was tiny (|A| = 1–7) while the last-edge
  frontier was rich (|B| = 27–60) — so a second intermediate, not deeper
  search, was the fix.
- **A verification-wrapper bug** (`*` vs `◇`) rejected five correct proofs;
  root-caused as a statement-fidelity failure, not a mathematical one, and
  now the centerpiece of the pack's §8 record.
- **Duality** measured zero lift on order-4 and real lift on order-5 — a
  reminder that a null result is distribution-indexed.

## 5. Honest limits

- Every score in this pack is a **ceiling** (verified components; judge-exact
  toolchain) — not an official-judge run. One production run converts it.
- The released-set 800/800 leans on pair-keyed certificates for released
  rows; the organizers state those rows will not recur privately. Private-set
  strength rests on the generalizing tiers and the held-out FALSE evidence
  — and no private-set number is claimed.
- Two public FALSE pairs remain unresolved by any finite search we ran
  (orders exhausted are stated exactly). The FALSE format permits an infinite
  carrier — but such a certificate needs a genuine Lean proof rather than the
  finite `decideFin!` table; these two pairs fall outside both our finite
  search and EULER's proof-supported infinite parity recognizer, not outside
  the format.
- The runtime 3-hop tier's forward frontier is narrower than the dev-time
  version's (documented in the dependency map).

## 6. Attribution

Equational Theories Project data and problem corpus: Tao et al. Chain
technique: after the public Stage-2 leader ("the-prompter"), independently
reimplemented; Krympa-style reconstruction: Kondylidou et al. Completion:
Knuth & Bendix; Twee: Smallbone. Finite model finding: McCune (Mace4).
ATPs: E (Schulz), Vampire (Kovács & Voronkov).

Two commercial systems deserve more than a list entry, because the work
would look different without them. **Axle, by Axiom (Carina Hong and the
Axiom Math team)**, was this project's dev-time verification backbone: a
cloud Lean compile-check engine that let us validate candidate certificates
against the judge's exact toolchain (Lean v4.32.2) in seconds instead of a
forty-minute round trip — every certificate in this pack passed through it,
and both statement-fidelity failures documented in this pack were *caught*
as divergences surfaced by Axle runs. **Aristotle, by Harmonic**, proved 390
of the solver's hard TRUE implications during earlier development campaigns;
those kernel-checked proofs are embedded (and disclosed) as the solver's
Layer-1 certificate table. Neither system is called at runtime; both shaped
what the runtime carries.

Judge, harness, and goal statement: SAIR Foundation, open repository. AI assistance in development
and drafting is disclosed in the accompanying paper's tool disclosure and in
the trust framework; no system bears responsibility for what is asserted
here. Errors are ours.
