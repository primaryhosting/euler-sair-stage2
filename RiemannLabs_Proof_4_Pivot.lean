/-
  Riemann Labs — SAIR Mathematics Distillation Challenge
  Proof 4: Equation 404 implies Equation 4236

  Technique: Transitivity Through a Shared Pivot
  Elegance: Two different instantiations of the same hypothesis
            reach the same intermediate value from opposite directions.
            Their transitive composition yields the goal.

  The hypothesis says: for all x, y, z,  x ◇ y = (z ◇ z) ◇ z.

  Every product equals the constant c(z) = (z ◇ z) ◇ z. But since z is
  universally quantified, c is the same for every z. In particular:
    - h(x, y, z) says:                x ◇ y = (z ◇ z) ◇ z
    - h((z ◇ z) ◇ z, w, z) says:     ((z ◇ z) ◇ z) ◇ w = (z ◇ z) ◇ z

  Chaining forward then backward through the pivot (z ◇ z) ◇ z:
    x ◇ y  =  (z ◇ z) ◇ z  =  ((z ◇ z) ◇ z) ◇ w

  Hypothesis (Equation 404):
    ∀ x y z : G,  x ◇ y = (z ◇ z) ◇ z

  Goal (Equation 4236):
    ∀ x y z w : G,  x ◇ y = ((z ◇ z) ◇ z) ◇ w

  Proof: Forward through h, backward through h applied to the pivot.
-/
import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z w
  exact (h x y z).trans (h ((z ◇ z) ◇ z) w z).symm
