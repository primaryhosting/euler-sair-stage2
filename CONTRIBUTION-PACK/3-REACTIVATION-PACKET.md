# EULER — Reactivation Packet
*(built to §10 of "Mathematics in the Age of Mechanical Reproduction": the
companion artifact that holds what is needed to reconstruct why the
successful path works)*

Per the paper, three things that look identical on the page are kept apart
here: the **process-evidence trace** (contemporaneous, in `8-TRACE/`, cited
by filename), the **retrospective rationale** (this document — reconstructed
after the fact, useful and not evidence), and the **difficulty map** (§5
below). Nothing in this packet manufactures friction: every failed approach
listed here actually failed, on a dated record.

---

## 1. The governing proof idea — stated as an idea

An equational-implication problem has three separable difficulties, and the
solver's architecture is the observation that none of them should be solved
with the same tool:

**Direction is not a research question.** For the 4694 order-4 magma laws,
the Equational Theories Project already computed the complete implication
closure. Embedding it makes TRUE/FALSE *exact* where it applies — measured
600/600 against the competition's own answers — while the best language
model measures 69% on hard instances. The idea: *never ask a model for a
fact a table already knows.*

**FALSE is finite model finding, and models are promiscuous.** A single
finite magma satisfies a large family of laws. So a small bank of tables,
keyed by which *hypotheses* each satisfies, refutes far more implications
than it was harvested for — the measured held-out result (120/120; 100/100
on never-released hypotheses) is the empirical form of this idea. When the
bank misses, a backtracking finite-model search over the operation table
(forward checking, symmetry breaking) is the general fallback. Soundness is
never delegated: every table is re-checked against both equations by a full
finite evaluation before it is emitted, and the judge's `decideFin!`
re-proves it in Lean.

**TRUE is rewrite reachability — until it isn't, and then it factors.**
Most true implications are closed by a rewrite chain from the hypothesis.
The residue falls to three factorings, in escalating order:
- through an *intermediate law* (transitivity: prove `i ⇒ k` and `k ⇒ j`
  where both are directly provable, compose);
- through a *collapse lemma* (Knuth–Bendix completion derives a projection
  law such as `a = a ◇ b`; a fixed construction then yields total collapse
  `∀ a b, a = b`, from which any equation follows by instantiation);
- through an *ATP's own derivation, replayed* (E's superposition proof is
  reconstructed node-by-node as named Lean `have`s; the machine's proof
  becomes the human-checkable proof).

**The meta-idea, which is the paper's:** the author never certifies his own
work. Every artifact is emitted only after an independent check — a finite
evaluation, a self-recheck of the chain, a total (valid-if-emitted)
completion prover, or the Lean kernel itself — and the competition's
deterministic judge is the final arbiter of every answer.

## 2. Pivotal lemmas, marked as pivotal

| Lemma / fact | Why it is pivotal |
|---|---|
| **Closure fact:** the 10,657 public explicit-proof edges generate, under transitivity, *all* 8,178,279 order-4 TRUE pairs (recomputed; missing 0, extra 0) | Licenses the transitivity tier: any order-4 TRUE pair factors through provable hops. |
| **Projection lemma L10** (`a = a ◇ b`), derived by completion for hypothesis 1689 | The chain engine could derive it but not *use* it — the goal needs `∀ a b, a = b`, which is a symm/trans construction, not a rewrite. Seeing that distinction produced the collapse-finisher. |
| **E-lemmas c_0_11** (`(a◇b)◇c = b◇(a◇c)`) **and c_0_13** (`a◇(a◇(b◇c)) = b◇c`) for hypothesis 3591 | Two instantiations finish the one problem every search-based method missed: `(z◇z)◇(x◇y) = z◇(z◇(x◇y)) = x◇y`. The ATP had the proof; reconstruction made it readable. |
| **Const-collapse emission template fix** (pin every binder to the left reduct except the constant's slot) | Turned the completion prover from ~30% emission reliability into *total* — valid-if-emitted — which is what makes it safe in the judge-less Marathon track. |
| **`subst_flat` termination fix** (one-pass simultaneous substitution) | A rule matching a subterm with swapped variables produced a cyclic substitution and an infinite walk; the fix made the prover terminating under a hard deadline. |

## 3. Failed approaches that materially explain the successful one

Each failure below is on the dated record and *changed the design*; none is
decorative.

1. **LLM direction.** Best model 69% on hard direction (public Stage-1 grid,
   25 models × 3 repeats); most sit at the base rate. → Direction moved
   entirely to the embedded closure. (The competition's own benchmark
   supplied the refutation.)
2. **LLM proving of structural TRUEs.** Frontier models 0/6 on the
   structural family. ATPs proved all six in milliseconds. → The proving
   stack is deterministic; models appear only as a last-tier fallback behind
   the judge gate.
3. **Chain rewriting on collapse laws.** Saturates: a projection/collapse
   goal is not reachable by rewriting the hypothesis. → Completion tier.
4. **Two-hop-only transitivity.** On the eight-problem residue, the forward
   provable-edge frontier |A| was 1–7 while the backward frontier |B| was
   27–60; the lone success had |A|=19. The bottleneck was proving the *first*
   edge — so deeper search does not help; a second intermediate does. →
   3-hop meet-in-the-middle; then ATP replay for what remained.
5. **Duality on order-4: zero lift** (measured on 90 pairs). Retained
   anyway, gated to unknown-direction inputs — where it then cracked two
   order-5 problems. The lesson, recorded: a measured null on one
   distribution is not a null on another.
6. **Deep chain at depth 10 / 1500 s** on the final problem: saturated in
   seconds — rewriting *cannot* bridge it with those lemmas. → E-prover
   shared-DAG replay, which does not search at all.
7. **A measurement-harness fidelity failure** (the `*`/`◇` operator bug —
   see `4-STATEMENT-FIDELITY.md`): five mathematically-correct proofs
   rejected by our own verification wrapper. Root-caused before any
   conclusion about the mathematics was drawn.

## 4. Dependency map — including the surprising dependencies

- `solver.py` → **ETP `outcomes.json`** (direction bitmatrix; byte-identical,
  0 disagreements on recomputation) and **`equations.txt`** (naming
  intermediate laws).
- Emitted certificates → the judge's `Magma` class **only**. *Surprising:*
  no certificate depends on Mathlib; the judge's own modules import only
  core Lean, so certificate validity is independent of the library the
  lakefile pins.
- Completion-prover validity → **nothing external**: emission is total, so
  its correctness does not depend on judge availability. *Surprising and
  load-bearing:* the Marathon track has no runtime judge (output is scored
  after exit), so only total/self-rechecking tiers are allowed to write there.
- 3-hop tier → *surprising narrowness, disclosed:* its forward frontier
  draws from the 2-hop candidate list (`bit(i,k) ∧ bit(k,j)`), which is
  stricter than all successors of `i`. The dev-time finder used the wider
  frontier. Recorded as a known limitation rather than silently differing.
- Dev-time only (never at runtime): Mace4, Vampire, E, **Axle (Axiom's
  cloud Lean compile-check engine — the verification gate every certificate
  in this pack passed through, on the judge's exact toolchain)**, and
  **Aristotle (Harmonic's Lean theorem prover — source of the 390 embedded
  Layer-1 proofs)**. Only their *outputs* — literal tables, kernel-checked
  proof texts, and compile verdicts — are embedded or relied on, and every
  embedded artifact is independently re-verified.

## 5. Difficulty map

Of 800 released problems, 784 fell to the organic tiers under conservative
budgets. The 16-problem residue, by what finally resolved each:

| Problems | Resolution | Difficulty character |
|---|---|---|
| 3 (1 order-4, 2 order-5) | Budget escalation only (transitivity k=40; 12-round completion + duality) | Cap artifacts, not hard problems |
| 387⇒4544 | 3-hop transitivity | Path exists; needed a second intermediate |
| 5 pairs (2666⇒2062 …) | Vampire-trace reconstruction | Rewrite-search-hard, ATP-easy |
| 1689⇒2391 | Collapse-finisher construction | The genuinely conceptual step: rewriting cannot express `∀ a b, a = b` |
| 3591⇒3820 | E-prover DAG replay | Hardest for search; trivial once the machine's own derivation is replayed |
| 8 order-5 TRUE | Deeper completion + ATP replay (parallel work) | Outside the oracle; the generalizable engine reaches 90–96/100 organically |

Two public FALSE pairs remain unresolved by any finite search performed
(`1167⇒1763`: no model through order 8; `2531⇒4307`: orders 2–6 exhausted,
order 7 timed out). No completeness claim is made.

## 6. Recorded explanation, and the machine-verifiable artifact

- **Explanation:** `6-DEMONSTRATION.md` — a self-contained expert-level
  exposition, including one pivotal proof worked in full, written to be
  delivered as a talk and checkable by any competent reader without access
  to the authors (the paper's "make the demonstration the artifact").
- **Machine-verifiable artifacts:** `2-SOLVER/solver.py` (every emitted
  answer is a Lean certificate the open judge re-verifies) and the eight
  loop-produced certificate bodies in `8-TRACE/*.json`, each checked against
  Lean v4.32.2 commit `f3b06c705…` — the judge's exact toolchain.
- **Process-evidence trace:** `8-TRACE/true_misses.json` (the dated
  miss-characterization, with per-problem escalation outcomes) and the four
  solved-body files, exactly as produced during the improvement loop, before
  this narrative existed. Absent cryptographic timestamps the claim is the
  comparative one the paper licenses: a contemporaneous record is stronger
  provenance than a retrospective narrative, and both are supplied.
