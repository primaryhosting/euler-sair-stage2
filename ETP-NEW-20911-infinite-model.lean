import Mathlib
set_option maxHeartbeats 4000000

namespace CM20911

/-- Countermodel for Equational Theories Project law 20911:
    `x = (y ◇ y) ◇ (((z ◇ x) ◇ x) ◇ z)`.
    A piecewise-linear magma on ℚ satisfying the law while `∀ x y, x = y` fails,
    so law 20911 does NOT imply Eq2 (x = y).  This law has no finite model
    (checked to order ~19 by Mace4) and no linear model over any ℤ/n; the model
    below is genuinely infinite. -/

class Magma (α : Type _) where op : α → α → α
infix:65 " ◇ " => Magma.op

/-- op(x,y) = x - y/2  if 0 ≤ x ∧ y < 0
             (x-y)/2   if x < 0 ∧ y < 0 ∧ y < x   (i.e. x > y)
             x - y     otherwise. -/
def m (x y : ℚ) : ℚ :=
  if 0 ≤ x then (if y < 0 then x - y/2 else x - y)
  else (if y < 0 then (if y < x then (x - y)/2 else x - y) else x - y)

instance Q : Magma ℚ := ⟨m⟩

theorem law_holds : ∀ x y z : ℚ, x = (y ◇ y) ◇ (((z ◇ x) ◇ x) ◇ z) := by
  intro x y z
  show x = m (m y y) (m (m (m z x) x) z)
  set a := m z x with ha
  set b := m a x with hb
  set c := m b z with hc
  set e := m y y with he
  rw [m] at ha hb hc he
  show x = m e c
  rw [m]
  split_ifs at ha hb hc he ⊢ <;> linarith

theorem eq2_fails : ¬ (∀ x y : ℚ, x = y) := by
  intro h; have h01 := h 0 1; norm_num at h01

theorem not_law_implies_eq2 :
    ¬ (∀ (G : Type) [Magma G],
        (∀ x y z : G, x = (y ◇ y) ◇ (((z ◇ x) ◇ x) ◇ z)) → (∀ x y : G, x = y)) := by
  intro H
  exact eq2_fails (H ℚ law_holds)

end CM20911

#print axioms CM20911.not_law_implies_eq2
