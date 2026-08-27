# Sediment and Technique
## A two-solver study of machine mathematics in the SAIR Equational-Theories Challenge

**Christopher Brock**
Riemann Labs · `chrisbrock54@gmail.com`

*Draft — 2026-08-26. Companion to "Mathematics in the Age of Mechanical
Reproduction" (Brock, 2026), whose reactivation standard this paper is written
to satisfy. Prepared around the SAIR Foundation Mathematics Distillation
Challenge, Equational Theories, Stage 2.*

---

## Abstract

We report a **paired exploratory case study** on a single, sharply-posed
machine-mathematics task: given two equational laws over a magma, decide whether
the first implies the second, and emit a Lean proof or a finite countermodel that
an open, deterministic judge accepts. We built two solvers for it that differ
*primarily* in one factor — embedded mathematical knowledge — while also differing
in codebase, prover tiers, prompt, and size; this is an approximate ablation, not
a clean single-variable one, and we read its results accordingly. **EULER** carries
the discipline's accumulated *sediment* — the
public Equational Theories Project's precomputed implication closure, a harvested
bank of finite countermodels, and hundreds of pre-verified proofs — behind a
cascade of deterministic provers. **WILL** carries none of it: no direction
oracle, no banks, no borrowed certificates, only *technique* distilled into
algorithms and a single prompt. Same problem, same judge, same author; the only
difference is whether the solver remembers what the field already worked out.
The gap between them measures how much of a "solve" is knowledge and how much is
method. We situate the two against the wider Stage-2 field, which has split into
LLM-steering and precompute-first camps, and we report every figure with an
explicit verification badge and the honest separation the accompanying paper
demands: a released-set *ceiling* that leans on exact-row certificates, kept
apart from the *held-out* and *reproducible* evidence that actually generalizes.
The contribution is the experiment and its epistemic packaging as much as the
solvers: a demonstration that the "distillation" the challenge asks for can be
made a measurable quantity rather than a slogan.

---

## 1. The problem

A **magma** is the most lawless object in algebra: a set `G` with one binary
operation `◇ : G × G → G` and no axioms at all. An **equational law** is a
universally quantified identity in `◇` — for example, law 1689 of the Equational
Theories Project (ETP) catalog, `∀ x y z. x = (y ◇ x) ◇ ((x ◇ z) ◇ z)`. Given an
ordered pair of laws `(E1, E2)`, the Stage-2 task asks whether `E1 ⊨ E2`: does
*every* magma satisfying `E1` satisfy `E2`? By Birkhoff's completeness theorem,
semantic implication over the class of all magmas coincides with derivability in
the equational calculus, so the question has a definite answer and a syntactic
witness.

The challenge fixes the currency of answers, and it is unusually strict. A
**FALSE** answer exhibits a finite operation table `t : Fin n × Fin n → Fin n`
satisfying `E1` and violating `E2`, which the judge re-decides mechanically
(`decideFin!`). A **TRUE** answer is a Lean 4 term of the goal type
`∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G`, kernel-checked under Lean
v4.32.2 (pinned commit `f3b06c705…`), with axioms restricted to
`{propext, Quot.sound, Classical.choice}` and placeholder/metaprogramming/unsafe
tokens rejected. The solver runs in a bare `python:3.11-slim` sandbox — 2 vCPU,
2 GB, no network, one source file ≤ 500 KB, 3600 s per problem — and reaches an
LLM and the Lean judge only through organizer-managed proxies. There is no
partial credit; the judge's verdict is the only score.

Two features make this an unusually clean laboratory. First, **verification is
free and perfect**: the judge will not accept an invalid proof, and being checked
costs the solver nothing. That removes the usual confound — "is the answer even
right?" — and moves all the interest onto *how* correct certificates get produced
at scale. Second, the task has a **public knowledge base**: the ETP has computed
and released the full pairwise implication closure for the 4,694 order-4 laws.
This is precisely the sediment whose value we want to measure. A solver may
embed it or refuse to; the challenge's own framing — *distillation* — asks which
techniques generalize once the lookup table is taken away.

## 2. The standard we hold ourselves to

Terence Tao's 2026 ICM criterion states flatly that a proof no human can properly
explain should be viewed as incomplete *even when a computer has formally
verified it*. The companion paper, *Mathematics in the Age of Mechanical
Reproduction*, reads that criterion through a 1936 constellation — Husserl on how
a technique outlives the insight it records, Benjamin on the trace, Turing on the
faculty he bracketed — and separates six relations that institutions usually run
together: correctness, statement fidelity, reactivability, access, standing, and
significance. Formal verification settles only the first. The others govern
whether a result is *knowledge*, not merely a checked artifact.

From that paper we take three obligations, and this study is written to meet them:

- **Statement fidelity (§8 there).** Verification adjudicates statement→proof and
  is silent on problem→statement. We disclose the two fidelity failures we caught
  in our own tooling (§9 here) and the guard we added.
- **Reactivation (§10 there).** A result should ship the governing idea, the
  pivotal steps, the failures that materially explain the successes, and the
  machine-verifiable artifact — so a competent reader, not just the kernel, can
  recover its sense. This paper, its cited pack, and the reproducible evidence
  are that packet.
- **Epistemic badges.** Every figure wears its verification status. We use
  *computationally verified* (exhaustive finite check), *verified
  (judge-toolchain)* (compiles on the judge's exact Lean), *ceiling* (composed of
  verified parts, not an official-judge run), and *official* (an organizer
  verdict — which no figure here yet carries).

The distinctive move of this study is to turn the challenge's word "distillation"
into a measurement. If technique is what survives when the deposit is removed,
then building the same solver with and without the deposit *measures* how much of
the performance was technique.

## 3. Method: an AI-assisted stack, and its pipeline

Both solvers were produced by a development pipeline that used AI systems and
classical tooling as *instruments*, never as unverified authorities. The
distinction is load-bearing: everything any instrument produced was independently
re-verified before it was trusted, and re-verified again by the judge at answer
time.

**Dev-time stack.** Public ETP data supplied the direction closure and the law
texts. Classical automated theorem provers — E (Schulz), Vampire (Kovács &
Voronkov) — and a finite-model finder, Mace4 (McCune), produced proofs and
countermodels whose *outputs* (not the tools) were embedded. **Aristotle**
(Harmonic's Lean theorem prover) proved several hundred hard implications.
**Axle** (Axiom — Carina Hong's team) compile-checked every candidate certificate
on the judge's exact Lean v4.32.2 toolchain in about two seconds, against a
forty-minute playground round trip; this made the measurement discipline
practical, and both fidelity failures below surfaced as Axle divergences. An
orchestration layer (large-language-model agents, including the author's own
tooling) drove the search, the reconstruction, and the drafting.

**Runtime stack.** Neither solver calls any of those dev-time tools at run time.
What ships is a single Python file: a parser and finite evaluator, a set of
deterministic provers, an embedded prompt for the organizer-provided model, and
— for EULER — the embedded public data and pre-verified certificates. The
pipeline's shape is the same for both solvers; the difference is only what the
runtime is allowed to *carry*.

## 4. Two solvers, one primary variable

The study varies *primarily* one factor: **embedded mathematical knowledge**
(the sediment). The problem, the judge, the sandbox, the author, the soundness
discipline, and the pipeline shape are held fixed. But the two are separate
implementations — they also differ in codebase, in the exact set and tuning of
prover tiers, in prompt, and in size — so this is an *approximate* ablation, not
a clean single-variable one. A true ablation (one codebase, a single feature flag
disabling only the matrix/proof-bank/countermodel-bank, both configurations run
on the identical manifest with every certificate compiled) is the natural next
step; we flag it as future work and read the present gap as suggestive, not
causal-isolating.

- **EULER** embeds the sediment: the 4,694² ETP implication bitmatrix (direction,
  exact on the order-4 core), a 305-table hypothesis-keyed countermodel bank, and
  a set of pre-verified Lean certificates (26 hand-derived, 390 by Aristotle, 18
  by ATP reconstruction). Behind that it runs a cheapest-first cascade of
  deterministic provers.
- **WILL** refuses the sediment. No implication matrix, no banks, no borrowed
  certificates. It grows countermodels from nothing, walks rewrite chains, grinds
  a law to its collapse, and calls the model from a single prompt teaching the
  moves as schemas. Its whole inventory is algorithm plus prompt.

Both obey the same invariant, which is the accompanying paper's §8 made
operational: **no answer counts unless the judge accepts it.** The deterministic
tiers additionally self-check before emitting; the heuristic tiers (a generic
tactic attempt, and the LLM) reach the judge as unverified guesses, gated only by
its acceptance. In the judge-less Marathon track, only self-verifying tiers may
write at all.

The prediction, stated in advance: **WILL scores below EULER, and the gap is the
measurement.** A perfect score built on a lookup table proves the table, not the
solver. Strip the table away, and what survives is technique.

## 5. EULER — precomputed knowledge

EULER is built from three refusals (developed in the companion solver paper; here
in brief).

**Direction is a table, not a question.** The ETP closure decides TRUE/FALSE
exactly for every order-4 pair; EULER reads it in constant time. *Badge:
computationally verified* — its embedded matrix agrees with the organizers'
published evaluation answers **600/600** on the three order-4 subsets. The
contrast that motivates embedding, rather than predicting, direction: on the
public Stage-1 benchmark the best of twenty-five large language models reaches
**69%** direction accuracy on hard instances, most at the base rate.

**FALSE is finite model finding, and witnesses are promiscuous.** One magma
satisfies a large family of laws, so a 305-table bank keyed by *hypothesis*
refutes far more pairs than it was built from; a pure-stdlib backtracking finder
(orders 4–8) covers novelty, and an infinite parity-walk tier reaches
countermodels no finite table can. Every emitted table is exhaustively
self-checked, and the judge re-decides it.

**TRUE is rewrite reachability until it isn't, and then it factors.** Chains
handle the easy majority; bounded Knuth–Bendix completion cracks the
collapse/constancy laws (its emission is *total* — valid if it emits);
transitivity composes proofs through intermediate laws, licensed by a recomputed
fact (the closure of the 10,657 public proof edges equals all 8,178,279 order-4
TRUE pairs); and ATP replay reconstructs an E/Vampire proof node-by-node into
human-checkable Lean.

## 6. WILL — distilled technique

WILL is the technique-only counterpart — an approximate ablation, not a clean
one (it is a separate implementation). It keeps EULER's *ideas* and discards
EULER's *deposits*.
Its inventory:

- A **counterexample search** that grows structured tables (constant, projection,
  cyclic) from formulas at run time, checks each against both laws exhaustively,
  and perturbs cells until the goal breaks. No stored bank.
- A **matching-chain prover** that treats the hypothesis as a rewrite rule and
  self-rechecks every chain before emitting.
- A **completion / collapse** engine: when the hypothesis forces a projection law,
  WILL constructs total collapse (`∀ a b, a = b`) from two instantiations of the
  hypothesis and closes any goal in one `exact`.
- An **LLM tier** driven by one embedded prompt that teaches the three moves as
  *schemas* — the shape of each technique, with no worked answer to any specific
  problem. (An earlier draft embedded three concrete worked examples; an
  adversarial review flagged that as smuggled verdicts contradicting the
  no-memorized-answers claim, and they were replaced with schemas. That correction
  is itself an instance of the fidelity discipline of §9.)

Every WILL exit is verified before submission exactly as in EULER; in Marathon,
only its self-verifying tiers write.

## 7. The field: two philosophies, one judge

The public Stage-2 field, at the time of writing, has divided into two design
philosophies, and naming them clarifies what our two solvers are.

- **LLM-steering.** A representative strong entry lets a language model *steer*
  mechanically-verified tools — proposing lemma bridges and model searches that
  are treated as untrusted hints and proven before use. It carries no direction
  oracle and reaches infinite countermodels via symbolic Nat-models, a capability
  worth noting; it is genuinely sound, and hostage to a weak proxy model on
  direction.
- **Deterministic-with-escalation.** Other entries run honest deterministic cores
  (rewrite chains, bridge routes, finite-model families) with an LLM escalation,
  skipping rather than guessing when the machinery cannot reach.

EULER is the precompute-first pole of this space; WILL is its own control, sitting
closer to the deterministic pole but stripped even of the oracle. Both terminate
at the same deterministic judge. The axis that separates *our* two entries is not
soundness — all of these designs are sound — but **reproducibility**: EULER's and
WILL's results regenerate without any model in the loop, from public materials,
on a laptop. That is the companion paper's thesis instantiated, and it is what
lets the EULER-vs-WILL gap be read as a measurement rather than a mood.

## 8. Results

All figures below are *computationally verified* or *verified (judge-toolchain)*
and, where composed into a headline, marked *ceiling*. None is an *official*
result: the promotion gate is a fresh organizer-judge run, which had not returned
at the time of writing (the last attempt hit an organizer-side infrastructure
error, documented and reported). We keep the released-set ceiling and the
held-out evidence rigorously apart.

### 8.1 EULER

| Claim | Value | Badge |
|---|---|---|
| Direction vs official answers (order-4 sets) | **600 / 600** | computationally verified |
| Held-out FALSE — pairs absent from every released set (seed 12345) | **120 / 120** | computationally verified, reproducible |
| Held-out FALSE — novel hypotheses (seed 999) | **100 / 100** | computationally verified, reproducible |
| Order-5 set, fully outside the oracle | **190 / 200** organic | computationally verified |
| Released evaluation sets (4 × 200) | **800 / 800** | **ceiling** |

The released 800/800 is a *ceiling* built partly from exact-row certificates for
released rows; the organizers state those rows will not recur privately, so it is
not a private-set claim. The figure that generalizes is the held-out result,
which is **reproducible** from a seeded program with immutable cohort manifests
(`evidence/held-out-cohorts/`), zero invalid witnesses.

### 8.2 WILL — the technique-only counterpart, on its mechanical tiers

WILL was benched with **no LLM and no oracle** on 100 released problems — a
balanced 50-FALSE / 50-TRUE sample from `evaluation_normal`, deterministic seed —
to see what *technique alone* recovers. This is a floor, not a ceiling: the LLM
tier operates only inside the competition sandbox and is unmeasured here. The
bench was re-run on the **import-repaired** solver (see §9); manifest, output
log, and every emitted certificate are bundled in `evidence/will-bench/`.

| Tier | Result |
|---|---|
| FALSE (`find_counterexample`) | **50 / 50** found; every table independently re-checked as a genuine finite countermodel (0 invalid) |
| TRUE (chain, then collapse) | **34 / 50**; 16 unsolved |
| FALSE cert shape (full `decideFin!` preamble, post-repair) | **50 / 50** |
| Combined | **84 / 100 answered, 0 answers disagreeing with ground truth** |

The FALSE certificates are verified three ways: cert shape, independent
finite-model re-check (exactly what the judge's `decideFin!` re-decides), and
**actual compilation under Lean v4.32.2 — the judge's exact toolchain — via
Axle** (Axiom's judge-exact cloud compiler). We compiled 15/15 constructed FALSE
certs and 6/6 real released FALSE certs; two deliberately-broken certs were
rejected 2/2 (the check has teeth). Details and reproduction in
`evidence/will-bench/GATE1-JUDGE-STATUS.md`. We still do **not** claim "100%
precision" as *official*: the organizer badge requires an organizer judge run.
What is established is that the certificate mechanism is judge-compilable on the
exact toolchain, no emitted answer disagreed with ground truth, and every FALSE
table is a sound countermodel.

A detail worth keeping: WILL's collapse tier proves **order-5 TRUEs more easily
than mid-difficulty normal ones** (15/20 of the order-5 TRUEs), because deeper
laws more often force constancy — technique, unlike a lookup table, has its own
grain that does not track "difficulty" as labeled.

### 8.3 The gap, read as a measurement

Set the two side by side, on the axis that varies:

- **FALSE side — technique nearly closes the gap.** EULER's bank gives instant
  coverage and 120/120 held-out; WILL's pure search gives 50/50 on its bench and
  0 invalid. Finite countermodel-finding is *portable*: the sediment buys speed
  and a small tail, not correctness the technique could not reach. This is the
  study's cleanest positive result — the FALSE-side "distillation" is real, and
  most of the deposit is compressible back into method.
- **TRUE side — this is where the deposits appear to pay.** EULER's oracle plus
  pre-verified certificates take the released TRUE side to its ceiling; WILL's
  technique alone recovers 34/50 (68%) mechanically, with the residue the deep
  proofs that completion and chains did not construct within budget. The gap on
  TRUE is *consistent with* the difference being accumulated proof rather than
  re-derivable move — but, because the two solvers differ in more than the one
  variable (§4), this study does not isolate that as the cause.

The one-sentence finding: **on this task, technique substantially reproduces the
FALSE side and about two-thirds of the TRUE side; the observed residual is
consistent with an advantage from accumulated certificates, but the present
design does not isolate that cause** — the residue is the deep, specific proofs a
from-scratch solver did not re-derive within budget, and a true single-flag
ablation (§4) is needed to attribute it. That is a concrete, reproducible
observation about the challenge's implicit question, and it is the kind of
ablation the field has mostly asserted rather than measured.

## 9. Derivation, fidelity, and reproducibility

**How it was derived.** The design was forced, in order, by measurements anyone
can repeat: the public closure decides direction exactly and models cannot, so
direction is embedded (EULER) or refused as a control (WILL); a FALSE answer is a
finite magma, so generate, verify, embed, and — for WILL — search; many TRUE
implications are rewrite chains, and the residue is completion and factoring. The
full recipe uses only the public ETP repository, any finite-model finder, any
Lean v4.32.2 environment, and the public judge — hours of laptop compute.

**Fidelity, on the record.** Verification is silent on whether the *statement*
checked is the statement intended. We caught two failures in our own tooling and
disclose them: a dev-time verifier whose hand-built goal differed from the
judge's binding, which *accepted* proofs the judge rejected; and an operator-glyph
mismatch (`*` vs `◇`) that *rejected* five correct proofs. Both times the checker
was flawless. A third guard followed the adversarial reviews: the solver now
binds every equation ID to the supplied equation text before trusting any
ID-keyed path — the judge builds the theorem from the text, so an ID that names a
different law is rejected, closing the same drift class.

**Reproducibility.** The held-out cohorts are not prose: a seeded generator
(`reproduce_heldout.py`) regenerates the exact pairs (held out from every released
set by construction) with an immutable result log. Both solvers ship with their
embedded data fully disclosed and each certificate re-verifiable; both were
subjected to two independent adversarial audits (a red-team pass and a second,
deeper one) whose findings — disclosure gaps, an invariant overclaim, the ID/text
drift — were fixed and are recorded.

## 10. Limitations

We state what is not established. (1) No private-set performance figure is
offered; the pair-keyed certificate layers are regression coverage only. (2)
WILL's LLM tier is unmeasured here — its bench is a technique-only floor. (3) Two
public FALSE pairs remain unresolved by any *finite* search we ran. The judge's
FALSE format itself permits an infinite carrier — the goal quantifies over an
arbitrary magma `G`, not only `Fin n` — but such a certificate needs a genuine
Lean proof of the hypothesis and the refutation rather than the mechanical
`decideFin!` a finite table gets; EULER's proof-supported infinite parity tier
closes this shape for the hypothesis families it recognizes, and these two pairs
fall outside both our finite search and that recognizer, not outside the format.
(4) The
soundness invariant is an audited structural property, not a machine-checked
theorem about the program; the judge's per-answer verification is the guarantee.
(5) All figures are ceilings on the judge's exact toolchain, not official runs;
the gap between EULER and WILL is measured on our sets and should be re-measured
on the private set when it is available.

## 11. Conclusion

The SAIR challenge asks for distillation — techniques that generalize once the
answer table is removed. We built the removal into the experiment. EULER carries
the discipline's sediment; WILL walks in without it; the gap between them, on the
same problem and the same judge, is a measurement of how much of machine
mathematics on this task is remembered knowledge versus re-derivable method. The
answer we find — technique reproduces the FALSE side and most of the TRUE side,
with a residue of deep proofs that stay sediment — is itself only half of what a
Stage-2 result worth making under Tao's criterion owes. The other half is
reactivation: the certificates, the failure history, the fidelity decisions, and
the verification status of every claim, shipped as first-class artifacts so a
competent reader can recover the sense that makes the result knowledge. We built
the solvers to answer the questions; we packaged them, and we ran the experiment,
to answer the harder one.

---

## References

- E. Husserl, *The Crisis of European Sciences* (incl. "The Origin of Geometry"), 1936.
- W. Benjamin, "The Work of Art in the Age of Mechanical Reproduction," 1936.
- A. M. Turing, "On Computable Numbers," 1937; "Systems of Logic Based on Ordinals," 1939.
- A. Jaffe and F. Quinn, "'Theoretical Mathematics'," *Bull. AMS* 29 (1993).
- W. P. Thurston, "On Proof and Progress in Mathematics," *Bull. AMS* 30 (1994).
- D. Knuth and P. Bendix, "Simple Word Problems in Universal Algebras," 1970.
- N. Smallbone, Twee; W. McCune, Mace4; S. Schulz, E; L. Kovács & A. Voronkov, Vampire.
- T. Tao et al., *The Equational Theories Project*, github.com/teorth/equational_theories.
- T. Tao, *Mathematics in the Age of AI*, ICM, 2026.
- T. Klowden & T. Tao, "Mathematical methods and human thought in the age of AI," 2026.
- *The Leiden Declaration on Artificial Intelligence and Mathematics*, 2026.
- C. Brock, *Mathematics in the Age of Mechanical Reproduction*, 2026 (the standard applied here).
- SAIR Foundation, *Mathematics Distillation Challenge — Equational Theories, Stage 2*, open judge repository.

## Acknowledgments

**Axle — Axiom (Carina Hong and the Axiom Math team)** verified every embedded
certificate on the judge's exact toolchain and surfaced both fidelity failures.
**Aristotle — Harmonic** proved 390 of EULER's hard TRUE implications. With the
Equational Theories Project (Tao et al.) and the classical stack (Knuth–Bendix,
Twee, Mace4, E, Vampire). None is a runtime dependency; all shaped what the
runtime carries; everything any of them produced was independently re-verified
before the judge saw it. AI assistance in development and drafting is disclosed;
no system is an author, and errors are the author's.

## Artifacts

EULER `solver.py` (442,061 B, SHA-256 `e0f7ac84…48329`) and WILL `solver.py`
(91,230 B, SHA-256 `90aa400c…bc66a`); the reproducible held-out cohorts; the
statement-fidelity record; the epistemic-badge table; and the companion white
paper. Every load-bearing claim here either cites a checkable artifact or names
the check it awaits.
