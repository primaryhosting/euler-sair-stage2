# EULER v8.1 finalization record

Status: **frozen final pre-submit candidate**.

The file to upload, renamed byte-for-byte to `solver.py`, is:

- `EULER-SUBMISSION-2026-08-25.py`
- 442,061 bytes
- SHA-256
  `e0f7ac8406f48c3054bea202cb1fbac1fb4988d6643551d2e9617d62c9b48329`
- 62,598 bytes below the 500,000-byte submission limit

Do not upload `EQT02-S00021-infra-failfast.py`; that is the intentionally
unchanged prior live mirror. It remains available as a rollback.

## Frozen evidence

- Python compilation is clean.
- The exact final binary passed the pinned official Python-image smoke under
  the published amd64, no-network, read-only, 2-CPU, 2-GB, 64-PID, and
  64-MB-`/tmp` restrictions.
- Integrated released-set regression: 800/800 (400 TRUE, 400 FALSE). This is a
  public-set ceiling, not a private-set or live-judge claim.
- All 400 captured released TRUE certificates compiled under exact Lean
  4.32.2 in the completed certificate audit.
- Every released finite FALSE witness was independently rechecked before
  emission.
- The new deterministic infinite FALSE certificate and the structured-plan
  fixture both compile through AXLE/Axiom on Lean 4.32.2; both axiom audits
  report trusted with no axioms or extra axioms.
- The infinite parity recognizer matches zero released rows and therefore did
  not inflate the 800/800 regression.

## Promotion gate

The playground has no remaining credits. Consequently, this candidate has not
replaced the live mirror and is not described as officially accepted.

When one official run becomes available:

1. Verify the file hash before upload.
2. Upload these exact bytes as `solver.py`.
3. Run one representative Solo problem.
4. Promote/copy over the live mirror only after an `accepted` judge result.
5. If the judge reports an infrastructure/module-header failure, keep the
   candidate frozen and use the existing infra-failfast evidence; do not
   modify proof logic in response to a host failure.

## Deliberately deferred research

Runtime superposition, generic collapse certificates, expanded infinite-model
families, stronger CSP propagation, and Marathon lemma learning remain
separate research directions. None is being merged into this frozen build
without held-out measurement and AXLE validation.

Checksums for the frozen candidate, rollback, and infinite-model validation
fixtures are recorded in `EULER-v8.1-FINAL.sha256`.
