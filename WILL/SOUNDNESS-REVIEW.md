# WILL v6 — Adversarial Soundness Review

Target: `WILL-v6-CANDIDATE.py` (2,342 lines)
Claim under attack: **"no code path exists from unverified guess to submitted answer."**
Reviewer stance: refutation. Every judge submission and Marathon write was traced to the
independent check that precedes (or gates) it.

**Verdict: SOUND** — with 5 flags (none produces a wrongly-ACCEPTED judge verdict or an
unverified Marathon write; two are letter-of-the-claim violations worth fixing).

Reading of the claim used: an "answer" is (a) a judge submission that could be *accepted*,
or (b) a Marathon output record (no judge at runtime). For (a) the judge's Lean
compilation is itself an independent mechanical check, which the file's own header
sanctions ("LLM output judge-gated"). For (b) there is no external check, so only
locally verified results may be written — this is where the claim must be airtight,
and it is.

---

## 1. Trace of every judge submission (`_attempt_judge` call sites)

| # | Site | What is submitted | Independent check preceding it | Status |
|---|------|-------------------|-------------------------------|--------|
| 1 | solve Tier 0 (L1976-1981) | `lean_true(triv["body"])` | `trivial_true`: alpha-canonical equality of Goal vs H (`_alpha_canon`, L1763) or syntactic `lhs == rhs` for `rfl` (L1765). Mechanical, computed. Judge also compiles. | OK |
| 2 | solve Tier 1 (L1984-1990) | `lean_false(n, table)` | `run_ce_search` (L1807) re-checks every returned table with `table_is_counterexample` (exhaustive over all assignments) regardless of which search produced it. Registered hook `_hook_ce_search` additionally passed `self_check_false` inside `find_counterexample` (L443-446). Double-checked, then judge `decideFin!` triple-checks. | OK |
| 3 | solve Tier 2 (L1993-1998) | chain body | `_hook_chain` → `chain_prove`: found chain is re-walked by `verify_chain` (L975-977) before emission; `_finalize_chain_body` re-verifies after noop-dropping (L1049); `calc_lines` re-applies every step at render time and raises on disagreement (L852-871). | OK (see Flag 3 re: `self_verified` not checked) |
| 4 | solve Tier 3 (L2001-2006) | collapse body | `collapse_prove`: every KB lemma re-walked at registration (`_register`, L1215 — unverifiable candidates dropped, "the lemma store can never contain an underived statement"); final pass re-verifies ALL needed lemma chains + the ALLEQ chain again (L1409-1414); `calc_lines` defense-in-depth at emission. | OK (see Flag 3) |
| 5 | solve Tier 4 (L2009-2014) | `intro …\ngrind` | **None locally — this IS an unverified guess sent to the judge.** Gate = judge Lean compilation: `grind` either kernel-checks a real proof of Goal or the submission is rejected. Cannot produce a wrong accept. | OK by judge-gate (letter-of-claim caveat, see Verdict note) |
| 6 | `_llm_rounds` false_table (L2056-2059) | `lean_false(n, table)` | `table_is_counterexample` before submission (exhaustive; also validates shape/int-range against LLM-supplied `n`, incl. ragged Pass-2 salvage tables). Judge `decideFin!` double-checks. | OK |
| 7 | `_llm_rounds` goal_proof (L2064-2069) | LLM proof body | `normalise` + `proof_body_is_clean` (banned-token screen), then judge compilation as the real verifier. `lean_true` indents every body line by 2 spaces so the body cannot escape the `by` block. | OK (see Flag 1: screen incomplete) |
| 8 | `_llm_rounds` bridge (L2073-2082) | `bridge_prove` spliced body | The lemma statement is never trusted: `chain_prove(H ⇒ lemma)` and `chain_prove_multi(H+lemma ⇒ Goal)` must BOTH verify (each chain independently re-walked) or the route returns None (L1029-1036). Judge compiles the splice. | OK (see Flag 2: screen bypassed) |
| 9 | solve Tier 6 CE (L2023-2029) | `lean_false` | Same double-check as #2. | OK |
| 10 | solve Tier 6 hooks (L2030-2036) | chain/collapse bodies | Same as #3/#4. | OK |

## 2. Trace of every Marathon write (`_marathon_solve_one`, no judge at runtime)

| # | Write | Independent check | Status |
|---|-------|-------------------|--------|
| 1 | trivial TRUE (L2119-2120) | `triv.get("self_verified")` checked; verification is the alpha-canon / syntactic-rfl computation itself. | OK |
| 2 | FALSE table (L2121-2124) | `run_ce_search` exhaustive re-check (`table_is_counterexample`), plus `self_check_false` inside the engine. | OK |
| 3 | chain/completion TRUE (L2125-2129) | `out.get("self_verified")` **is** checked here (unlike solve — see Flag 3); registered hooks only set it after `verify_chain`. | OK |
| — | LLM tier | Disabled entirely in Marathon. No path. | OK |
| — | Exceptions | `except Exception: ans = None` (L2107-2109) — a crash can never write a partial/unverified record. | OK |

No Marathon write exists that is not preceded by an exhaustive table re-check or a
`verify_chain` re-walk. The claim holds where it matters most.

## 3. `*` → `◇` normalization on every emission path

- Problem equations: `prep_problem` normalises both (L1689-1690); all deterministic
  bodies are rendered via `p_render`/`render` which hard-code `OP = "◇"`. ✓
- LLM proof bodies: `normalise(sug.get("proof",""))` at L2066, explicitly commented
  "Boundary rule holds even for model output". ✓
- LLM lemma: `normalise(lemma)` at L2076, and `bridge_prove` re-normalises via
  `p_parse_equation`. ✓
- FALSE certificates: tables are ints — no operator to normalise. ✓
- Tier 4 grind / trivial bodies: variable names come from tokenizers that reject `*`
  (would raise), operating on already-normalised text. ✓
- Non-str proof values (e.g. `{"proof":123}` via legacy dialect passthrough in
  `_normalize_sug`): `normalise` returns non-str unchanged, `proof_body_is_clean`'s
  `isinstance` check rejects. No crash, no emission. ✓

**No emission path can carry a `*` into Lean code.** Verified exhaustively.

## 4. Banned-token screen

`_BANNED_TOKENS = (sorry, admit, sorryAx, mkSorry, #eval, run_tac, macro, elab,
syntax, unsafe, implemented_by, dbg_trace)` — substring check, applied at L2067 only.

- Deterministic bodies are built from a closed grammar (intro/have/calc/congrArg/
  exact + rendered terms) and cannot contain these tokens — except via Flag 2 below.
- LLM raw bodies: screened. Bodies that pass are still judge-compiled.

## 5. PROMPT no-oracle check

- `{problem.*}` / `{solver.analysis}` / `{solver.feedback}` are runtime interpolations;
  `build_analysis` derives everything from the equations in hand. ✓
- Generic technique statements ("projection laws … force collapse") are law-CLASS
  heuristics, not per-law verdicts. ✓
- **But see Flag 4:** the three worked miniatures are literal (H, Goal, verdict,
  proof/table) triples.

---

## FLAGS (ranked)

**Flag 1 — `native_decide` (and kin) absent from `_BANNED_TOKENS`.** An LLM proof body
containing `native_decide` passes `proof_body_is_clean` and reaches the judge. If the
judge environment permits it, acceptance rests on compiled-code evaluation rather than
the kernel alone (widened TCB). Mitigation in context: the TRUE Goal here
(`∀ G [Magma G], H → eq`) is not decidable, so `native_decide` cannot close it absent a
decidability-instance bug — practical risk ≈ nil, but the screen's intent is violated.
Recommend adding `native_decide`, `ofReduceBool`, `reduceBool`.

**Flag 2 — bridge path bypasses the banned-token screen (letter-of-claim violation).**
`bridged` (L2076-2081) goes to `_attempt_judge` without `proof_body_is_clean`. LLM-chosen
lemma *variable names* survive parsing verbatim (`_p_tokenize` accepts any alnum/_/'
identifier — `sorry`, `admit`, `unsafe`, `dbg_trace` are all valid variable names) and
are emitted as Lean binders (`∀ (sorry : G)`, `intro sorry`). So "banned Lean tokens
cannot be emitted" is FALSE on this path. Not a soundness hole: these are Lean keywords,
so the submission fails to parse/compile and the judge rejects; a binder of type G can
never prove a Prop even where it shadows. Fix: run `proof_body_is_clean(bridged)` before
submission, or reject lemma variable names in the banned set.

**Flag 3 — `solve()` ignores the `self_verified` hook flag.** Tiers 2/3/6 submit
`out["body"]` unconditionally; only Marathon honors the flag (L2119, L2127). With the
in-file registered hooks this is moot (they always verify before returning), but the
`register_prover` plug-point lets a third-party prover ship an unverified body straight
to the judge. Judge compilation still prevents a wrong accept, but the hook-contract
asymmetry contradicts the "no unverified exit" comment. Fix: `if out and
out.get("self_verified")` in solve, matching Marathon.

**Flag 4 — PROMPT worked miniatures are literal per-law verdicts (no-oracle, borderline).**
The three miniatures each embed a concrete (H, Goal) pair with its full answer:
(1) `x = y◇y ⊢ x = (y◇x)◇z` TRUE + proof; (2) `x◇y = y ⊢ (x◇y)◇z = z` TRUE + proof;
(3) `x◇y = y◇x ⊬ x◇x = x` FALSE + table `[[1,0],[0,0]]`. These are pedagogical
few-shot examples, but strictly read they ARE memorized verdicts for three specific
implications — contradicting the header's "no memorized verdicts of any kind." If any
contest problem coincides (or alpha-matches) one of these pairs, the prompt hands the
model the answer. Everything is still mechanically verified downstream, so soundness is
unaffected; this is a competition-honesty exposure. Fix: replace with pairs provably
outside the contest law numbering, or state them as schemas rather than instances.

**Flag 5 — infra-detection false positive (availability, not soundness).**
`_judge_result_is_infra` matches the substrings `"incompatible header"` /
`"JUDGE_INFRASTRUCTURE"` anywhere in the serialized judge result. An ordinary rejection
whose error detail happens to quote either string (e.g. the judge echoing submitted code
or an olean-related type error) permanently latches `_JUDGE_INFRA_DOWN` and halts all
further judging for the run. Cannot cause a wrong answer — it only forfeits attempts.

## Attacks attempted that FAILED (claim held)

- Forged chain args: `_successors` fills unbound rule vars from a pool (`pool[0]`
  fallback, L924) and `_normal_form` fills with `sub` (L1129) — but `apply_step`
  reconstructs the substitution from the recorded args and checks the rewrite site
  exactly, so any wrong arg kills `verify_chain` and the exit is refused.
- KB lemma laundering: `_register` drops any candidate whose canonical chain fails
  re-walk (L1215); dependency `_closure` emits `have` ladders in creation order, so no
  forward references; `collapse_prove` re-verifies every needed chain a second time.
- Emission drift: `calc_lines` re-applies each step during rendering and raises;
  `collapse_prove` catches and returns None ("emission disagreed … refuse", L1428).
- Ragged/short LLM tables, `n` mismatch, non-int cells: shape-validated in both
  `self_check_false` and `table_is_counterexample` before any emission.
- Escaping the `by` block via multi-line proof body: `lean_true` indents every
  non-blank line by 2 spaces; no line can dedent to top level.
- Marathon crash-path write: exceptions map to `ans = None`; nothing partial is written.
- Name collision (goal variable literally named `h`, `ALLEQ`, `L1`): can shadow and
  break Lean *compilation* (judge rejects; Marathon record fails to grade) — a
  robustness bug, but the abstract verdict was verified, so never an unsound accept.

## Bottom line

Every path that can produce an **accepted** judge verdict or a **written** Marathon
record is preceded by an independent mechanical check: exhaustive table re-evaluation
(FALSE), `verify_chain` re-walk + render-time re-application (deterministic TRUE),
alpha-canon/syntactic triviality (trivial TRUE), or judge Lean compilation (LLM/grind
TRUE). The literal claim is only violable in the harmless direction: unverified
*attempts* (grind, raw LLM bodies, hypothetical unverified third-party hooks) do reach
the judge, where rejection — not acceptance — is the worst case. Fix Flags 1-3 to make
the letter of the claim match the code; reconsider Flag 4 before entry.
