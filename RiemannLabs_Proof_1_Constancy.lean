/-
  Riemann Labs — SAIR Mathematics Distillation Challenge
  Proof 1: Equation 3268 implies Equation 3253

  Technique: Direct Constancy Substitution
  Elegance: One line. The free variable y in the hypothesis is set to x,
            collapsing the equation into the goal.

  The hypothesis quantifies over (x, y), but y appears only on the right-hand
  side. Since y ranges over all elements, we may choose y := x. The resulting
  equation is identical to the goal.

  This is the purest form of the constancy principle: a universally quantified
  variable that appears on only one side of an equation can be instantiated
  freely without loss of generality.

  Hypothesis (Equation 3268):
    ∀ x y : G,  x ◇ x = y ◇ (x ◇ (x ◇ x))
    (y is free — appears only on the RHS)

  Goal (Equation 3253):
    ∀ x : G,  x ◇ x = x ◇ (x ◇ (x ◇ x))

  Proof: Instantiate h with y := x.
-/
import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x
  exact h x x
