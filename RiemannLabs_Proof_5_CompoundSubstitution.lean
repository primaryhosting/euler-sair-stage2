/-
  Riemann Labs — SAIR Mathematics Distillation Challenge
  Proof 5: Equation 282 implies Equation 2133

  Technique: Compound Term Substitution
  Elegance: The hypothesis has a free variable z that absorbs arbitrary
            structure. By instantiating z with the compound term (z ◇ w),
            the hypothesis literally becomes the goal.

  This is the deepest form of constancy: the free variable z in the
  hypothesis is not merely set to another variable — it is set to a
  compound expression (z ◇ w) built from the goal's variables. The
  magma operation ◇ appears inside the substitution itself, weaving
  new structure into the equation.

  Where Proof 1 substitutes a variable for a variable (y := x),
  this proof substitutes a *term* for a variable (z := z ◇ w).
  The universality of the hypothesis — "for all z" — makes this
  legal. A single element, a product, an iterated tower — all are
  valid inhabitants of z.

  Hypothesis (Equation 282):
    ∀ x y z : G,  x = ((y ◇ y) ◇ x) ◇ z
    (y and z are free — absent from the LHS)

  Goal (Equation 2133):
    ∀ x y z w : G,  x = ((y ◇ y) ◇ x) ◇ (z ◇ w)

  Proof: Instantiate h with z := (z ◇ w).
-/
import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z w
  exact h x y (z ◇ w)
