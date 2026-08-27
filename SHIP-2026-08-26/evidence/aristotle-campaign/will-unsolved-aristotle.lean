import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/
theorem evaluation_normal_0100 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ y) ◇ (x ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (z ◇ z) ◇ y := by
  intro x y z
  have e0 := h x (y ◇ (y ◇ y)) x
  have e1 := h (x ◇ x) z x
  have e2 := h (y ◇ y) (y ◇ (y ◇ y)) y
  have e3 := h (z ◇ z) (y ◇ (y ◇ y)) z
  have e4 := h ((y ◇ y) ◇ y) (y ◇ (y ◇ y)) ((z ◇ z) ◇ z)
  have e5 := h ((z ◇ z) ◇ z) y ((z ◇ z) ◇ z)
  have e6 := h ((z ◇ z) ◇ z) z (x ◇ (z ◇ z))
  have e7 := h ((z ◇ z) ◇ z) z ((z ◇ z) ◇ z)
  have e8 := h ((z ◇ z) ◇ z) (y ◇ (y ◇ y)) (x ◇ x)
  have e9 := h ((z ◇ z) ◇ z) (y ◇ (y ◇ y)) ((x ◇ x) ◇ x)
  grind

/- evaluation_normal_0082: eq857 → eq3670 -/
theorem evaluation_normal_0082 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ z) ◇ (y ◇ y)))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ y) ◇ (z ◇ x) := by
  intro x y z
  have e0 := h y y y
  have e1 := h y y (x ◇ x)
  have e2 := h y (x ◇ x) x
  have e3 := h z y y
  have e4 := h z (x ◇ y) (x ◇ y)
  have e5 := h z (z ◇ x) (z ◇ x)
  have e6 := h (x ◇ x) x y
  have e7 := h (x ◇ x) x (x ◇ y)
  have e8 := h x x ((z ◇ y) ◇ (z ◇ z))
  have e9 := h x y (y ◇ y)
  have e10 := h x z ((y ◇ y) ◇ (y ◇ y))
  have e11 := h x (x ◇ x) (x ◇ (x ◇ x))
  have e12 := h (y ◇ y) y y
  have e13 := h (y ◇ y) y z
  have e14 := h (y ◇ y) (y ◇ y) ((y ◇ z) ◇ (y ◇ y))
  have e15 := h (z ◇ z) ((z ◇ x) ◇ y) ((x ◇ y) ◇ y)
  have e16 := h (z ◇ z) ((z ◇ x) ◇ y) ((z ◇ x) ◇ y)
  have e17 := h (z ◇ z) ((z ◇ x) ◇ z) ((z ◇ y) ◇ (z ◇ z))
  grind

/- evaluation_normal_0012: eq532 → eq608 -/
theorem evaluation_normal_0012 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (y ◇ (z ◇ (w ◇ x))))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ (w ◇ (u ◇ x))) := by
  intro x y z w u
  have e0 := h x z w u
  have e1 := h x (y ◇ (z ◇ (w ◇ (u ◇ x)))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (z ◇ (w ◇ (u ◇ x)))
  have e2 := h (z ◇ (w ◇ (u ◇ x))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (z ◇ (w ◇ (u ◇ x))) y
  have e3 := h (z ◇ (w ◇ (u ◇ x))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (z ◇ (w ◇ (u ◇ x))) z
  have e4 := h (y ◇ (z ◇ (w ◇ (u ◇ x)))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (y ◇ (z ◇ (w ◇ (u ◇ x))))
    (z ◇ (w ◇ (u ◇ x)))
  grind

/- evaluation_normal_0084: eq868 → eq438 -/
theorem evaluation_normal_0084 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ ((y ◇ z) ◇ (w ◇ u)))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (y ◇ (x ◇ z))) := by
  intro x y z
  have e0 := h x (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z)))
  have e1 := h (y ◇ (y ◇ (x ◇ z))) y (y ◇ (x ◇ z)) y (y ◇ (x ◇ z))
  have e2 := h (y ◇ (y ◇ (x ◇ z))) y (y ◇ (x ◇ z)) (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z)))
  grind

/- evaluation_normal_0112: eq2546 → eq4209 -/
theorem evaluation_normal_0112 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((y ◇ y) ◇ z)) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ y) ◇ x) ◇ y := by
  intro x y z
  have e0 := h (z ◇ y) ((z ◇ y) ◇ x) x
  have e1 := h ((z ◇ y) ◇ x) x x
  have e2 := h ((z ◇ y) ◇ x) x ((z ◇ y) ◇ x)
  have e3 := h x ((z ◇ z) ◇ z) x
  have e4 := h x ((z ◇ z) ◇ z) ((z ◇ z) ◇ z)
  have e5 := h ((z ◇ z) ◇ z) (x ◇ ((x ◇ x) ◇ x)) ((z ◇ z) ◇ z)
  have e6 := h ((z ◇ z) ◇ z) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x))
  have e7 := h (x ◇ ((x ◇ x) ◇ x)) x x
  have e8 := h (x ◇ ((x ◇ x) ◇ x)) x (z ◇ y)
  have e9 := h (x ◇ ((x ◇ x) ◇ x)) x ((z ◇ y) ◇ x)
  grind

/- evaluation_normal_0044: eq3366 → eq3390 -/
theorem evaluation_normal_0044 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ (y ◇ x)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ (z ◇ w)) := by
  intro x y z w
  have e0 := h x y (x ◇ y)
  have e1 := h x (z ◇ (x ◇ (z ◇ w))) z
  have e2 := h y x (z ◇ (x ◇ (z ◇ w)))
  have e3 := h y (z ◇ (x ◇ (z ◇ w))) (z ◇ (x ◇ (z ◇ w)))
  have e4 := h z w x
  have e5 := h z w z
  have e6 := h z w (x ◇ (z ◇ w))
  have e7 := h z (z ◇ (x ◇ (z ◇ w))) z
  have e8 := h w z x
  have e9 := h w z z
  have e10 := h w z (x ◇ (z ◇ w))
  have e11 := h w z (z ◇ (x ◇ (z ◇ w)))
  have e12 := h (z ◇ (x ◇ (z ◇ w))) x z
  have e13 := h (z ◇ (x ◇ (z ◇ w))) x w
  have e14 := h (z ◇ (x ◇ (z ◇ w))) y (x ◇ y)
  have e15 := h (z ◇ (x ◇ (z ◇ w))) y (z ◇ (x ◇ (z ◇ w)))
  have e16 := h (z ◇ (x ◇ (z ◇ w))) z w
  have e17 := h (z ◇ (x ◇ (z ◇ w))) z (z ◇ (x ◇ (z ◇ w)))
  have e18 := h (z ◇ (x ◇ (z ◇ w))) (x ◇ y) x
  have e19 := h (z ◇ (x ◇ (z ◇ w))) (x ◇ y) y
  have e20 := h (z ◇ (x ◇ (z ◇ w))) (x ◇ (z ◇ w)) w
  have e21 := h (z ◇ (x ◇ (z ◇ w))) (z ◇ (x ◇ (z ◇ w))) y
  have e22 := h (z ◇ (x ◇ (z ◇ w))) (z ◇ (x ◇ (z ◇ w))) w
  grind

/- evaluation_normal_0104: eq2245 → eq4068 -/
theorem evaluation_normal_0104 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ x))) ◇ z)
    : ∀ (x : G) (y : G), x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
  intro x y
  have e0 := h x y x
  have e1 := h x y (x ◇ (x ◇ x))
  have e2 := h x (x ◇ (x ◇ (y ◇ x))) x
  have e3 := h x (x ◇ (x ◇ (y ◇ x))) y
  have e4 := h (x ◇ (x ◇ x)) (x ◇ (x ◇ (y ◇ x))) x
  have e5 := h (x ◇ (x ◇ x)) (x ◇ (x ◇ (y ◇ x))) y
  grind

/- evaluation_normal_0160: eq1883 → eq2250 -/
theorem evaluation_normal_0160 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ (y ◇ z)) ◇ (w ◇ u))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ z))) ◇ y := by
  intro x y z
  have e0 := h x y z (x ◇ (x ◇ (y ◇ z))) y
  have e1 := h y (x ◇ (y ◇ z)) ((x ◇ (x ◇ (y ◇ z))) ◇ y) (x ◇ (y ◇ z))
    ((x ◇ (x ◇ (y ◇ z))) ◇ y)
  have e2 := h x x (y ◇ z) (y ◇ x) x
  grind

/- evaluation_normal_0030: eq2064 → eq2876 -/
theorem evaluation_normal_0030 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G), x = ((x ◇ y) ◇ y) ◇ (y ◇ y))
    : ∀ (x : G) (y : G), x = ((x ◇ (y ◇ y)) ◇ y) ◇ y := by
  intro x y
  have e0 := h x (y ◇ y)
  have e1 := h (x ◇ (y ◇ y)) y
  have e2 := h (((x ◇ (y ◇ y)) ◇ y) ◇ y) (y ◇ y)
  grind

/- evaluation_normal_0024: eq1462 → eq4136 -/
theorem evaluation_normal_0024 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (z ◇ (x ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
  intro x y z w
  have e0 := h x x w
  have e1 := h x y y
  have e2 := h y (x ◇ y) (x ◇ y)
  have e3 := h z x x
  have e4 := h w (x ◇ y) (x ◇ y)
  have e5 := h x w (z ◇ x)
  have e6 := h (x ◇ x) (w ◇ (x ◇ x)) (y ◇ (x ◇ y))
  have e7 := h (x ◇ x) (w ◇ (x ◇ x)) (w ◇ (x ◇ y))
  have e8 := h (x ◇ x) (y ◇ (x ◇ y)) z
  grind

/- evaluation_normal_0018: eq1065 → eq3 -/
theorem evaluation_normal_0018 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (z ◇ z)) ◇ z))
    : ∀ (x : G), x = x ◇ x := by
  intro x
  have e0 := h x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))
  have e1 := h (x ◇ x) (x ◇ x) ((x ◇ x) ◇ (x ◇ x))
  have e2 := h (x ◇ x) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))
  have e3 := h (x ◇ (x ◇ x)) (x ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))
  have e4 := h ((x ◇ (x ◇ x)) ◇ x) x x
  have e5 := h ((x ◇ x) ◇ (x ◇ x)) ((x ◇ (x ◇ x)) ◇ x) ((x ◇ (x ◇ x)) ◇ x)
  have e6 := h ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ (x ◇ x)) ◇ x)
  grind

/- evaluation_normal_0004: eq134 → eq1400 -/
theorem evaluation_normal_0004 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ x) ◇ x))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((z ◇ w) ◇ x) ◇ x) :=
  fun x y z w => h x y (z ◇ w)

/- evaluation_normal_0130: eq844 → eq3725 -/
theorem evaluation_normal_0130 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ y) ◇ (x ◇ z)))
    : ∀ (x : G) (y : G), x ◇ y = (x ◇ y) ◇ (y ◇ y) := by
  intro x y
  have e0 := h (x ◇ y) ((y ◇ y) ◇ (y ◇ y)) (x ◇ y)
  have e1 := h (y ◇ y) y (x ◇ (x ◇ y))
  have e2 := h (y ◇ y) y ((y ◇ y) ◇ (x ◇ (x ◇ y)))
  have e3 := h (y ◇ y) (x ◇ y) ((x ◇ y) ◇ y)
  have e4 := h (y ◇ y) (x ◇ y) ((y ◇ y) ◇ (y ◇ y))
  have e5 := h ((x ◇ y) ◇ (x ◇ y)) (y ◇ y) ((y ◇ y) ◇ ((x ◇ y) ◇ y))
  grind

/- evaluation_normal_0168: eq2020 → eq1743 -/
theorem evaluation_normal_0168 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ w)) ◇ (z ◇ y))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((z ◇ y) ◇ y) :=
  fun x y z => (h x x x x).trans (h ((y ◇ y) ◇ ((z ◇ y) ◇ y)) x x x).symm

/- evaluation_normal_0184: eq2615 → eq4173 -/
theorem evaluation_normal_0184 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ z) ◇ w)) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ y) ◇ z) ◇ w :=
  fun x y z w => (h (x ◇ y) x x x).trans (h (((y ◇ y) ◇ z) ◇ w) x x x).symm

/- evaluation_normal_0038: eq2936 → eq23 -/
theorem evaluation_normal_0038 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G), x = ((y ◇ (y ◇ x)) ◇ x) ◇ x)
    : ∀ (x : G), x = (x ◇ x) ◇ x := by
  intro x
  have e0 := h x x
  have e1 := h x ((x ◇ (x ◇ x)) ◇ x)
  grind
