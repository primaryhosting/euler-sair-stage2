import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-!
## Countermodels

Two magmas are constructed below.

* `IntMagma`: the carrier is `ℤ` with `x ◇ w = -w` when `0 ≤ x` and `x ◇ w = 1 - w`
  when `x < 0`.  Both left translations are involutions, and the two sign regions are
  arranged so that equation 1167 holds while equation 1763 fails.
  (A countermodel here is necessarily infinite: in a *finite* magma satisfying
  equation 1167 all left translations coincide with one single involution, and then
  equation 1763 holds automatically.)

* `Z13Magma`: the carrier is `ZMod 13` with `x ◇ y = 7 * x + 7 * y`; it satisfies
  equation 2531 but not equation 4307.
-/

/-- Left translations of this magma: `w ↦ -w` for nonnegative left argument,
`w ↦ 1 - w` for negative left argument. -/
instance IntMagma : Magma ℤ where
  op x w := if 0 ≤ x then -w else 1 - w

theorem IntMagma_op (x w : ℤ) : x ◇ w = if 0 ≤ x then -w else 1 - w := rfl

/- false_hole_1167_1763: eq1167 ⊭ eq1763 (find a countermodel, finite or infinite) -/
theorem false_hole_1167_1763 : ∃ (G : Type) (_ : Magma G), (∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ y)) ◇ x)) ∧ ¬ (∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ z) ◇ x)) := by
  refine ⟨ℤ, IntMagma, ?_, ?_⟩
  · intro x y z
    simp only [IntMagma_op]
    split_ifs <;> omega
  · intro h
    have h0 := h 0 (-1) 1
    simp only [IntMagma_op] at h0
    norm_num at h0

/-- `x ◇ y = 7 * x + 7 * y` on `ZMod 13`. -/
instance Z13Magma : Magma (ZMod 13) where
  op x y := 7 * x + 7 * y

theorem Z13Magma_op (x y : ZMod 13) : x ◇ y = 7 * x + 7 * y := rfl

/- false_hole_2531_4307: eq2531 ⊭ eq4307 (find a countermodel, finite or infinite) -/
theorem false_hole_2531_4307 : ∃ (G : Type) (_ : Magma G), (∀ (x : G) (y : G), x = (y ◇ ((y ◇ x) ◇ x)) ◇ y) ∧ ¬ (∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = z ◇ (z ◇ y)) := by
  refine ⟨ZMod 13, Z13Magma, ?_, ?_⟩
  · decide
  · intro h
    have h0 := h 0 0 1
    simp only [Z13Magma_op] at h0
    revert h0
    decide
