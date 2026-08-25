# The Machine That Shows Its Work
*Telling I — for a curious twelve-year-old, or anyone at all*

---

Here is a game. You get to invent a way of combining things. Any way you
like. Take two things, combine them, get a thing back. We'll draw the
combining as a diamond: `a ◇ b` means "a combined with b."

Your way of combining doesn't have to be fair, or sensible, or anything.
`a ◇ b` does not have to equal `b ◇ a`. There are no rules — except the ones
you choose.

Mathematicians call an invented world like this a **magma**. (Really. It is
one of the best words in mathematics, and nobody knows for certain where it
came from.)

Now, the game. I hand you a rule, like this one:

> **Rule A:** for any x, y, z you pick, x is always equal to
> (y ◇ x) ◇ ((x ◇ z) ◇ z).

That looks like alphabet soup, and that's fine — the point is only that it's
a rule about how the combining behaves. And then I hand you a second rule,
Rule B, and I ask the question the whole game turns on:

**If a world obeys Rule A, does it *have* to obey Rule B?**

Not "does it usually." Not "in the worlds we've checked." *Have to.* Every
possible world, including ones no person will ever think of.

There are two ways to answer, and they are beautifully different.

**To answer NO,** you just need to build one world. One combining table —
even a tiny one with three or four things in it — that obeys Rule A and
breaks Rule B. One counterexample world, and the argument is over. Anyone
can check your table by hand.

**To answer YES** is harder, because you can't check every world — there
are infinitely many. You need a *proof*: a chain of reasoning showing that
Rule A drags Rule B along behind it, everywhere, always.

A competition asked a computer program to answer thousands of these
questions. Ours is called EULER, and it has three habits worth telling you
about, because they are good habits for people too.

**First: it looks things up before it thinks.** Mathematicians — a big team,
led by one of the most famous mathematicians alive — already worked out the
answers for thousands of these rule-pairs and published them for everyone.
EULER carries that table inside it. When someone has already done the work
carefully and shown it in public, you don't guess. You look it up. (We
tested the table against the competition's own answer key: six hundred
questions, six hundred right.)

**Second: it never gets to say "trust me."** Every answer EULER gives goes
to a judge — another program, written by the competition, that checks every
single step. If EULER answers NO, the judge rebuilds the counterexample
world and tests both rules on it. If EULER answers YES, the judge walks the
whole proof, line by line, and one bad line means the answer is thrown out.
EULER cannot bluff. There is no door in the program marked "just believe
me." We made sure of that, because the interesting thing was never getting
the right answer — it was getting answers *that show their work.*

**Third: it knows the difference between what it did and what that proves.**
When we say how well it scored, we say which parts were checked, and how,
and what has *not* been checked yet. That habit has a long name in our
other, more serious write-ups. Here it just has a short one: honesty.

---

Now the best part. One of the questions stumped every trick the machine
had — until it stopped being a search problem and became something you can
*see*.

Rule A above — the alphabet-soup one — looks harmless. It is not. Hidden
inside it is a trap that snaps shut on any world that obeys it.

The machine, grinding through consequences of Rule A, discovered a smaller
rule that A forces on you:

> **The bossy rule:** anything combined with anything is just the first
> thing again. `a ◇ b = a`. Always.

Sit with that. In a world where the bossy rule holds, combining does
nothing. And when you feed the bossy rule back into Rule A itself, the trap
closes: you can show that any thing `a` equals any other thing `b`. Every
single thing in the world is equal to every other thing.

The whole world collapses to a single point.

And in a one-point world, *every* rule is true — Rule B included — because
every statement of the form "this equals that" is just "the point equals
the point." Yes, Rule A forces Rule B. Not by a long clever chain from A to
B, but because A demolishes the world so completely that nothing is left to
go wrong.

Here is the part I want you to keep. The machine had already *found* the
bossy rule. It was holding the key. But its way of thinking — rewriting one
side of an equation, step by step, toward the other — can never say "and
therefore everything is everything." That's not a rewriting step. That's a
different *kind* of thought. A person looked at what the machine had
uncovered, saw what kind of statement it really was, and finished the proof
in three lines. Then — habit number two — the three lines went to the
judge, which checked them without caring in the slightest who wrote them.

Machines are extraordinary at searching. People are still the ones who
notice what a thing *is*. The future of mathematics, as far as we can tell,
is those two working honestly together — with a judge that checks
everybody, and no one, human or machine, ever getting to say "trust me."

That's the game, the machine, and the collapse. If you climb to the next
telling, the same story is waiting for you — closer up.
