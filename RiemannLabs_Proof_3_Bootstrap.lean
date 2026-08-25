/-
  Riemann Labs — SAIR Mathematics Distillation Challenge
  Proof 3: Equation 359 implies Equation 4065

  Technique: Self-Referential Bootstrap via calc chain
  Elegance: The hypothesis proves its own extension. Equation 359 says
            "the square equals the cube." Applying the operation (· ◇ x) to
            both sides of that identity yields "the cube equals the fourth
            power." Transitivity closes the chain.

  This is an instance of the *iterated absorption* pattern: if a = f(a),
  then a = f(a) = f(f(a)) = f(f(f(a))) = ... The equation bootstraps
  itself to arbitrarily deep nesting.

  Hypothesis (Equation 359):
    ∀ x : G,  x ◇ x = (x ◇ x) ◇ x
    "The square equals the cube"

  Goal (Equation 4065):
    ∀ x : G,  x ◇ x = ((x ◇ x) ◇ x) ◇ x
    "The square equals the fourth power"

  Proof:
    Step 1: h x                              gives  x ◇ x = (x ◇ x) ◇ x
    Step 2: congrArg (fun a => a ◇ x) (h x)         gives  (x ◇ x) ◇ x = ((x ◇ x) ◇ x) ◇ x
    Chain:  calc block connects them.
-/
import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x
  calc x ◇ x = (x ◇ x) ◇ x := h x
    _ = ((x ◇ x) ◇ x) ◇ x := congrArg (fun a => a ◇ x) (h x)
