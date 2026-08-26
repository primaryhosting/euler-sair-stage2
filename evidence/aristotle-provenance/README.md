# Aristotle (Harmonic) proof provenance

*Riemann Labs · 2026-08-26*

EULER embeds **390 TRUE proofs produced by Harmonic's Aristotle** during
development (the `_AB` zlib+base64 blob, decoded to `hardcoded_proof._aristotle`,
keyed `"eq1_id:eq2_id"`). They are dev-time contributors: embedded as literal Lean
bodies, disclosed, and **re-verified by the competition judge at answer time**.

## What is recorded here
- `aristotle-proofs-manifest.json` — the **exact 390 pairs**, each with the
  SHA-256 and length of its embedded Lean body. This fixes *what* is embedded so
  any drift from the frozen solver is detectable. Ids range 5..4682 (all order-4).

## What could and could not be re-verified here
- These 390 pairs have **zero overlap with the released eval sets** (they are a
  dev-time harvest for *other* order-4 TRUE pairs), so they cannot be re-compiled
  against a known judge problem text from the released data.
- Re-verifying them *in isolation* is not reliable, because reconstructing each
  proof's Goal requires the exact equation **text** the proof was written against,
  and EULER's internal `_eq_list()` catalog text for these ids does **not**
  reproduce it (see the open item below). In production this is a non-issue: the
  judge supplies the problem text, `bind_ids_to_text()` (the statement-fidelity
  guard) only trusts an id when the supplied text matches, and in Solo every emit
  is judge-gated.
- Per dev records, each body was **Axle-verified on the judge's exact Lean
  v4.32.2 at creation**; the FALSE-side Axle harness in this pack
  (`evidence/will-bench/gate1_axle_false.py`) demonstrates the same judge-exact
  toolchain is what we validate on.

## Job-level provenance — PULLED 2026-08-26 (`aristotle-job-records.json`)
We logged into the Aristotle account (`aristotle.harmonic.fun`, `ARISTOTLE_API_KEY`)
and pulled the source jobs. The 390 `_AB` proofs came from **11 `batch_all_*` jobs
run 2026-05-19 16:31 UTC** (project ids recorded), plus `retry_181` (2026-05-20)
and a `false_100` FALSE-side job. **Confirmation of the link:** job `batch_all_000`
(project `9a040def…`, task `9e664ddd…`) proved 50 magma implications; **49 of the
50 pairs are byte-present as keys in the embedded `_AB` blob**, and the single
non-`_AB` pair (`eq1900→eq1966`) is exactly the one that job reported UNPROVED
(`sorry`). That ties the embedded set to these dated jobs end-to-end.

## Note on the `_AB` key→text question (resolved)
The earlier observation that proof `5:625` introduces 4 variables while EULER's
`_eq_list()` id 625 has 3 is explained: the Aristotle **batches carried their own
equation texts** (a harvest selection, e.g. `problem_normal_0001 = eq2918→eq1911`),
and the batches used `import Mathlib` (`convert`/`congr!`/`exact?`). EULER's
embedded `_AB` bodies are the **re-derived Mathlib-free forms** (grind/have),
re-verified on the judge toolchain (Axle) before embedding. Pair-keys therefore
match the jobs while the proof text was adapted to the sandbox's no-Mathlib rule.
Integrity note retained: at runtime `bind_ids_to_text()` only trusts an id when
the supplied problem text matches EULER's `_eq_list()`, and Solo is judge-gated —
so a stale body cannot become an *accepted* wrong answer; in Marathon (no runtime
recheck) it would simply be scored-rejected.
