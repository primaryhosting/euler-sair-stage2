# Packet Changelog — SHIP-2026-08-27-FINAL vs SHIP-2026-08-26

*Assembled 2026-08-27. Base: SHIP-2026-08-26 (frozen). Deadline: 2026-08-31 AoE.*

## Added

1. **Entry 3: `solvers/EQT02-AUTOLAB.py`** (69,055 B, sha256 `b58a004b…e33683`).
   The DELIVERY-RUNBOOK of 2026-08-27 morning listed this entry as *BLOCKED on
   packaging (experiment `6f80ea8e`)*. That experiment has since **merged**
   (commit `fe5cb161` on the AutoLab project main): `scripts/build_solver.py`
   inlines laws + emitters + all tiers into a single file, and the hard
   acceptance test passed on the execution node — 12/12 answers accepted by the
   official `pipeline/runner.py`, 0 bad certificates, 0 harness imports.
   The file here is the verbatim `solver.py` from that merged main.
   Full provenance: `solvers/EQT02-AUTOLAB-PROVENANCE.md`.
2. **Entry 3 cover** in `SUBMISSION-NOTES.md` (description, embedded-data
   disclosure, honest scope) and the entry table row in `README.md`.
3. **`evidence/judge-infra/`** — the two 2026-08-20 judge-infrastructure bug
   reports (olean header mismatch; 100% `JUDGE_INFRASTRUCTURE_ERROR`), so the
   packet itself carries the reason no official-judge badge exists yet.
4. **`DELIVERY-RUNBOOK.md`** copied into the packet (upload steps travel with
   the packet).

## Reconciliations (documented, nothing rewritten)

- **Stale WILL hash.** The historical root file `EULER-v8.1-FINAL.sha256`
  records WILL as `5f1a174f…` — that entry is stale. The authoritative WILL
  hash is `90aa400c872cc071d19bb3786568d469ba4d703e5f467fa544756b254a639468`
  (91,230 B), used consistently by this packet's `CHECKSUMS.sha256`,
  `SUBMISSION-NOTES.md`, and the 08-26 FREEZE file.
- **Order-5: 190/200 vs 200/200.** Both appear in the corpus and both are
  true of different things: **190/200** is the generalizing-tier computation
  (FALSE 100/100, TRUE 90/100) — the number the covers use; **200/200** is
  reached only after 10 static ATP-proof replays are included
  (EULER-FINAL-README / methodology). The covers deliberately quote the
  conservative generalizing figure.
- **The "884/884" figure** in the root `ai-orchestrated-mathematics-whitepaper.md`
  is a vision-document figure not reconciled to the submission's 800/800-ceiling
  framing; that whitepaper is intentionally NOT part of this packet.

## Standing status (unchanged)

- EULER (`e0f7ac84…`, 442,061 B) and WILL (`90aa400c…`, 91,230 B) are byte-identical
  to the 08-26 freeze — unchanged.
- **No entry carries an OFFICIAL-judge badge.** Every headline number is
  held-out / computational on the judge's pinned toolchain. The one external
  gate remains SAIR playground credits; upload steps in `DELIVERY-RUNBOOK.md`.
