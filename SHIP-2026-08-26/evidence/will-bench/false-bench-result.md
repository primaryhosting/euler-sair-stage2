# WILL FALSE-side bench result

Technique-only (oracle-free) Marathon over 15 FALSE pairs, 20s/problem.
Each solved answer: cert carries full FALSE preamble + finOpTable + decideFin!,
and the table is independently re-checked as a genuine counterexample.
This is a shape + finite-model check, NOT an official-judge run.

- solved: 15/15
- cert shape OK (full preamble): 15/15
- countermodel independently re-verified: 0/15

| id | pair | verdict | cert shape | model recheck |
|---|---|---|---|---|
| wf00 | comm |= left-proj | FALSE | shape-OK | MODEL-BAD |
| wf01 | comm |= right-proj | FALSE | shape-OK | MODEL-BAD |
| wf02 | comm |= idempotent | FALSE | shape-OK | MODEL-BAD |
| wf03 | idempotent |= comm | FALSE | shape-OK | MODEL-BAD |
| wf04 | assoc |= comm | FALSE | shape-OK | MODEL-BAD |
| wf05 | left-proj |= comm | FALSE | shape-OK | MODEL-BAD |
| wf06 | left-proj |= right-proj | FALSE | shape-OK | MODEL-BAD |
| wf07 | comm |= assoc-collapse | FALSE | shape-OK | MODEL-BAD |
| wf08 | idempotent |= left-proj | FALSE | shape-OK | MODEL-BAD |
| wf09 | comm |= x=xx | FALSE | shape-OK | MODEL-BAD |
| wf10 | assoc |= idempotent | FALSE | shape-OK | MODEL-BAD |
| wf11 | right-proj |= left-proj | FALSE | shape-OK | MODEL-BAD |
| wf12 | comm |= right-collapse | FALSE | shape-OK | MODEL-BAD |
| wf13 | left-proj |= idempotent | FALSE | shape-OK | MODEL-BAD |
| wf14 | comm |= const | FALSE | shape-OK | MODEL-BAD |

## Corrected independent re-check (table parsed from emitted cert)

countermodel independently re-verified: **15/15**

| id | pair | carrier | model recheck |
|---|---|---|---|
| wf00 | comm |= left-proj | n=2 | model-OK |
| wf01 | comm |= right-proj | n=2 | model-OK |
| wf02 | comm |= idempotent | n=2 | model-OK |
| wf03 | idempotent |= comm | n=2 | model-OK |
| wf04 | assoc |= comm | n=2 | model-OK |
| wf05 | left-proj |= comm | n=2 | model-OK |
| wf06 | left-proj |= right-proj | n=2 | model-OK |
| wf07 | comm |= assoc-collapse | n=2 | model-OK |
| wf08 | idempotent |= left-proj | n=2 | model-OK |
| wf09 | comm |= x=xx | n=2 | model-OK |
| wf10 | assoc |= idempotent | n=2 | model-OK |
| wf11 | right-proj |= left-proj | n=2 | model-OK |
| wf12 | comm |= right-collapse | n=2 | model-OK |
| wf13 | left-proj |= idempotent | n=2 | model-OK |
| wf14 | comm |= const | n=2 | model-OK |
