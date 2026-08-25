# The Table, the Worlds, and the Judge
*Telling II — for the scientifically literate reader*

---

In 1936, Edmund Husserl described a quiet catastrophe that visits every
successful science: its methods get so good that they no longer need to be
understood to be used. The insight that built a technique drains away while
the technique keeps working — *works better than ever*, which is what makes
the loss invisible. He called the remedy reactivation: the labor of
recovering, from the machinery, the sense that made it knowledge.

Ninety years later, machines began writing mathematical proofs that no
human had read. Terence Tao, surveying this from the 2026 ICM, stated a
criterion that should stop anyone in the field: a proof that no human can
properly explain should be viewed as incomplete — *even when a computer has
formally verified it.* Correct, checked, and not yet knowledge.

This is the story of one small system built under that criterion, inside a
competition, on purpose.

## The problem

A magma is the most lawless object in algebra: a set, one binary operation
`◇`, no axioms whatsoever. An equational law is a universally quantified
identity — for instance law 1689 of a public catalog:

> ∀ x y z:  x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

The SAIR Mathematics Distillation Challenge, an outgrowth of Tao's
Equational Theories Project, poses thousands of questions of one shape:
*does every magma satisfying law E1 also satisfy law E2?* And it demands
answers in the strongest currency there is. Claiming NO requires a concrete
countermodel — a finite operation table the judge re-tests mechanically.
Claiming YES requires a formal proof in the Lean language, checked by the
competition's open, deterministic judge down to the kernel. No partial
credit. No reputation. The judge's verdict is the only score.

Notice what this setting does: it makes *verification* free and perfect,
and thereby moves all the interest to the questions verification cannot
answer. Which is exactly where Husserl said the interest would move.

## Three ideas

Our solver, EULER, is built from three ideas, each of which is really a
refusal.

**The refusal to guess what is known.** For the 4,694 laws of the catalog's
core, the Equational Theories Project already computed — and published —
the complete answer table: every pair, TRUE or FALSE, settled. EULER
carries that table verbatim, and so *knows* the direction of every core
question before it starts. We checked the embedded table against the
competition's own evaluation answers: 600 for 600. Contrast: on the
competition's public benchmark, the best of twenty-five large language
models guesses direction correctly 69% of the time on hard instances. A
model is a marvel; a table of settled mathematics is *settled mathematics*.
The design principle: never ask a model for a fact a table already knows.

**The refusal to trust its own cleverness.** Every answer EULER produces
passes an independent check before it is submitted — a counterexample table
is exhaustively re-tested against both laws; a proof chain is re-walked
step by step — and then the judge checks it *again*. There is no code path
from "EULER believes this" to "EULER submits this." Belief is not a
category the system has. This sounds like paranoia and is actually the
whole epistemology: in a world of cheap derivations, the discipline of
*showing* work is worth more than the work.

**The refusal to stop at one method.** NO-answers come from a library of
small worlds — a few hundred finite operation tables, each of which happens
to satisfy many laws at once, so a small library refutes a vast range of
implications; when the library misses, a search builds new worlds to order.
YES-answers climb a ladder: rewrite chains first; then a completion engine
that derives the deep consequences of a law; then proof-composition through
intermediate laws; and at the very top, replaying the internal derivations
of classical theorem provers, translated line by line into the judge's
language. Each rung is cheap-to-expensive, and each hands the judge its
work.

## The collapse

One question defeated the entire ladder, and its resolution is the best
thing in this story.

Does law 1689 — the identity above — force law 2391? Every search-based
method timed out or saturated. And they *should* have, because the truth of
the matter is not at the end of any chain of rewrites.

Grinding out consequences of 1689, the completion engine derived something
alarming:

> **L10:**  a = a ◇ b  — for *all* a and b.

Combining anything with anything returns the first thing. The operation is
a projection. Now watch what a human can do with that in three moves, none
of which is a rewrite. Take the original law at the values (a, b, a); it
says `a` equals a certain combination whose head is `b ◇ a`. But L10 says
that combination just *is* `b ◇ a`. So `a = b ◇ a`. And L10, read once
more, says `b = b ◇ a`. Two things equal to the same thing:

> **a = b.  For every a and every b.**

The world collapses to a point. And in a one-point world every equation
holds trivially — law 2391 included. The implication is true not because a
path leads from 1689 to 2391, but because 1689 annihilates every world it
touches.

Here is the Husserlian moment, stated plainly. The machine had *derived*
L10 — the decisive fact was in its hands — and could not finish, because
its language of thought (rewrite this into that) cannot express the
conclusion "all elements are equal." That is a different category of
statement. Seeing *what kind of statement the goal is* took a human act;
writing it down took three lines; and then the judge — caring nothing for
who wrote what — checked every line against the kernel. The division of
labor was not human *or* machine. It was: machine searches, human sees,
judge disposes. Each doing the thing the others cannot.

## The honesty budget

Every number this project reports wears a label, and the labels are the
point. The solver's perfect sweep of the released problem sets is labeled a
*ceiling* — it leans on certificates prepared for those released problems,
which the organizers say will not recur in the private evaluation, so we do
not claim it predicts private performance. The claims that *do* generalize
were measured on held-out problems the system had never been tuned on. Two
public questions we could not answer are named, with the exact bounds of
the searches that failed. And twice during development our own verification
tooling rejected correct proofs — or accepted proofs against a subtly wrong
statement of the goal — and both failures are documented in full, because a
checker can be perfect while the *statement it checks* is not the statement
you meant. That gap, between the problem and its formalization, is the one
place no verifier can save you. It deserves the daylight.

The tools deserve their names too: the Equational Theories Project's public
data, under Tao; Axiom's Axle engine — Carina Hong's team — which verified
every certificate against the judge's exact toolchain during development
and caught both of those fidelity failures; Harmonic's Aristotle prover,
whose 390 machine-proved implications ride inside the solver, disclosed
and re-checked like everything else; and the classical provers — Vampire,
E, Mace4 — whose derivations we replayed into human-checkable form.

Correct, checked, *and explained* — to you, just now. That was the
assignment. The next telling has the machinery; the last has the proofs.
