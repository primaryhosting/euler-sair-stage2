# Held-out FALSE cohorts — reproducible result log

Regenerate: `python3 reproduce_heldout.py` (deterministic; same seeds → same
cohorts → same result). Solver: `../EULER-SUBMISSION-2026-08-25.py`. Exclusion set:
bundled `released_index.json` (800 released pairs / 497 released hypotheses).

## Cohort A — held-out order-4 FALSE (seed 12345)
Selection: random order-4 pairs the embedded oracle calls FALSE, **excluding
every released-set pair** (800 excluded).
Size 120. **Solved 120/120**,
invalid witnesses 0. IDs in
`cohort_heldout_false.json`.

## Cohort B — novel-hypothesis order-4 FALSE (seed 999)
Selection: as above, additionally requiring the hypothesis id to appear in NO
released set (497 released hypotheses excluded).
Size 100. **Solved 100/100**,
invalid witnesses 0. IDs in
`cohort_novel_hypothesis.json`.

## What this establishes, and what it does not
Establishes: both cohorts are held out from every released set by construction;
selection is seeded and inspectable; every counted witness is a sound finite
countermodel (E1 holds for all assignments, E2 fails for some — re-checked here
and again by the judge's `decideFin!` if submitted). Does NOT establish
private-set accuracy, nor that these pairs mirror the private distribution.
Badge: COMPUTATIONALLY VERIFIED (witness soundness + held-out-by-construction),
not an official-judge or private-set result.
