# EULER v6 — Proof Reconstruction, Constructive Countermodels, and Austin Research

Date: 2026-08-30. This supersedes the earlier finite-structural-only diagnosis.

## Current banked results

| law | verdict | banked evidence | remaining gate |
|---|---|---|---|
| `order5_normal_0029` | FALSE | exhaustive order-6 table replay: antecedent 216/216; target fails 161/216 | compile the judge-shaped certificate on the official Lean 4.33.1 runner |
| `order5_normal_0030` | TRUE | E proof-object reconstructed by matching; independent Aristotle proof; both checked by AXLE on Lean 4.33.0 | official Lean 4.33.1 runner |
| `order5_normal_0036` | TRUE | E-derived right absorption; independent structured Aristotle proof; checked by AXLE on Lean 4.33.0 | official Lean 4.33.1 runner |

The TRUE results hold for every magma. They do not use finiteness. In particular,
0030 derives total collapse `∀ a b, a = b`, and 0036 derives right absorption
`∀ a b, a ◇ b = a`.

## Architecture

EULER v6 has three separate tracks. They share parsers and certificate gates but
must not blur their logical scopes.

### v6-A — General equational TRUE reconstruction

Use E as a proof searcher and reconstruct its proof object, rather than repeating
bounded term search inside the translator.

1. Run E with a rendered proof object and retain inference kinds and parent IDs.
2. Parse equations with explicit variable scopes and alpha-normalize each clause.
3. For every `spm`/rewrite step, recover orientation, position, and substitution by
   matching parent subterms against the rendered child.
4. Emit only kernel-checkable equality combinators: `congrArg`, `Eq.trans`, and
   `Eq.symm`, with local `have` declarations forming a deterministic DAG.
5. Prune unused clauses, scan the final judge payload, and compile it.

This is the abstraction that cracked 0030. Large intermediate terms are cheap once
the proof object's parent/child structure is used directly.

### v6-B — Constructive FALSE certificates

Search families in increasing cost and emit an explicit model for every decision:

1. small finite tables with constraint propagation and symmetry breaking;
2. affine/linear models over finite fields;
3. exact polynomial/Groebner constraints for structured operations;
4. nonlinear finite model search;
5. symbolic infinite families, including one-sided shifts and piecewise-rational
   operations.

Every candidate is checked against the parsed input equations before emission.
Finite tables use the judge's finite-operation certificate mechanism; infinite
models require an exact universal Lean proof. The 0029 order-6 table is the first
banked v6-B result.

### v6-C — Finite-structural Austin research

Finite-map reasoning remains valuable for statements whose hypotheses or targets
actually concern finite models. It is not a sound route to a universal implication
merely because only trivial finite models were found computationally.

Candidate machinery:

- definable subsets such as `im(◇)`, `im(L_a)`, and `im(R_a)`;
- one-sided inverse to two-sided inverse on finite subsets;
- finite translation injectivity/surjectivity conversion;
- orbit and eventual-periodicity lemmas;
- parameter erasure and finite-carrier collapse.

The motivating bridge remains the finite implication E3994 ⇒ E3588: on the
definable subset `S = im(◇)`, a one-sided inverse becomes two-sided because `S` is
finite. That theorem family belongs in v6-C, not in the universal 0030/0036 proofs.

## Austin-120 research matrix

The authoritative open set is materialized in the AutoLab workspace as 120 unique
laws: 96 laws with only trivial finite models known plus 24 laws whose finite-model
status is unknown. It forms 60 dual pairs. Ten confirmed Austin laws are kept as
controls, not counted among the 120.

The prior 12-agent workflow was an exploratory Group-3/residual run, not an
Austin-120 sweep. Its audited outcomes are:

- 0029: accepted order-6 countermodel;
- E13102: accepted piecewise-rational countermodel;
- E23357: rejected because the reported search and validator checked a malformed
  equation with an extra final multiplication by `z`.

The manifest, controls, audit, bounded router, and validator live under
`stress-eval/austin120/`. The router is resumable, atomically checkpointed, limited
to two workers, and guarded by host-memory, disk, and trivial-compile preflights.

## Pipeline ordering

1. normalize and validate the two input equations;
2. cheap rewrite/completion proof search;
3. v6-A E proof-object search and matching reconstruction;
4. v6-B finite and symbolic countermodel families;
5. v6-C finite-structural analysis only for logically finite tasks;
6. e-graph saturation as a bounded fallback;
7. static policy scan, size gate, exact-toolchain kernel check, and only then emit.

No search result is a decision until its submitted Lean certificate passes the
judge-shaped gate.

## Soundness and competition invariants

- No proof holes, custom axioms, unsafe escape hatches, or parser extensions.
- No answer tables, pair-keyed proof banks, target lists, or precomputed verdicts.
- General recognizers may derive witnesses from the input syntax at runtime.
- Every rewrite DAG is replayed independently before Lean emission.
- Every emitted certificate must compile on the official Lean/Mathlib 4.33.1
  toolchain. AXLE 4.33.0 checks are useful evidence but are not mislabeled as that
  final gate.
- Respect the current judge size and declaration policies; re-read them at release
  time instead of hard-coding assumptions into the research engine.
- Development-time E, Aristotle, and AXLE use is disclosed and never becomes a
  runtime dependency.

## Build plan

- P0: run the three banked residual payloads through the official 4.33.1 runner.
- P1: productionize v6-A parsing, matching, variable-renaming, orientation, DAG
  pruning, and deterministic Lean emission; keep 0030 as the regression fixture.
- P2: integrate the 0029 order-6 certificate and generalize v6-B nonlinear finite
  search without embedding the problem or its answer.
- P3: retain symbolic affine/shift recognition and add exact piecewise-rational
  emission, using E13102 as a reusable-method fixture.
- P4: build v6-C as an explicitly finite theorem library and evaluate it against
  the Austin manifest.
- P5: run normal 60/60, current official stress-200, size/allowlist, and parity
  gates. A regression or unverifiable certificate is discarded.
- P6: only after host preflight and freeze approval, submit the full resumable
  Austin-120 router to AutoLab compute.
