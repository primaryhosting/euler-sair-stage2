import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/
theorem heldout_true_000 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((y ◇ x) ◇ z)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ z) ◇ y) ◇ x) := by
  intro x y z
  exact (Eq.trans (h x ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) x) (Eq.trans (congrArg (fun t => t ◇ ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x)) (congrArg (fun t => ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (h (((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) ◇ x) (x ◇ (((y ◇ z) ◇ y) ◇ x)) (x ◇ (((y ◇ z) ◇ y) ◇ x)))))) (Eq.trans (congrArg (fun t => t ◇ ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x)) (congrArg (fun t => ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ (x ◇ (((y ◇ z) ◇ y) ◇ x))) (congrArg (fun t => (x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ t) (h x (x ◇ (((y ◇ z) ◇ y) ◇ x)) x).symm))))) (h (x ◇ (((y ◇ z) ◇ y) ◇ x)) ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) x).symm)))

/- heldout_true_001: eq3244 → eq579 -/
theorem heldout_true_001 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ w) ◇ w) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (z ◇ (z ◇ x))) := by
  intro x y z
  exact (Eq.trans (h x x x x) (h (y ◇ (z ◇ (z ◇ (z ◇ x)))) x x x).symm)

/- heldout_true_002: eq971 → eq759 -/
theorem heldout_true_002 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ y) ◇ (z ◇ w)))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((y ◇ x) ◇ z)) := by
  intro x y z
  exact (Eq.trans (h x x x x) (h (y ◇ (z ◇ ((y ◇ x) ◇ z))) x x x).symm)

/- heldout_true_003: eq1172 → eq262 -/
theorem heldout_true_003 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ z)) ◇ y))
    : ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ x) ◇ z := by
  intro x y z
  exact (Eq.trans (h x x x) (h (((x ◇ y) ◇ x) ◇ z) x x).symm)

/- heldout_true_004: eq1982 → eq4336 -/
theorem heldout_true_004 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ y)) ◇ (y ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = z ◇ (w ◇ z) := by
  intro x y z w
  exact (Eq.trans (h (x ◇ (y ◇ x)) x x x) (h (z ◇ (w ◇ z)) x x x).symm)

/- heldout_true_005: eq2099 → eq838 -/
theorem heldout_true_005 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ (x ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ x) ◇ (z ◇ x)) := by
  intro x y z
  have lem2 : ∀ (X Y : G), (X ◇ (X ◇ Y)) = X := fun X Y => (Eq.trans (congrArg (fun t => t ◇ (X ◇ Y)) (h X X X)) (h X (X ◇ X) Y).symm)
  have lem3 : ∀ (X Y : G), (X ◇ (X ◇ Y)) = (X ◇ Y) := fun X Y => (Eq.trans (congrArg (fun t => X ◇ t) (lem2 (X ◇ Y) x).symm) (Eq.trans (congrArg (fun t => t ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ x))) (lem2 X (X ◇ x)).symm) (Eq.trans (congrArg (fun t => t ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ x))) (congrArg (fun t => X ◇ t) (lem2 X x))) (Eq.trans (congrArg (fun t => t ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ x))) (congrArg (fun t => t ◇ X) (lem2 X Y).symm)) (h (X ◇ Y) X ((X ◇ Y) ◇ x)).symm))))
  exact (Eq.trans (lem2 x (x ◇ ((y ◇ x) ◇ (z ◇ x)))).symm (Eq.trans (congrArg (fun t => x ◇ t) (lem3 x ((y ◇ x) ◇ (z ◇ x)))) (lem3 x ((y ◇ x) ◇ (z ◇ x)))))

/- heldout_true_006: eq1193 → eq2383 -/
theorem heldout_true_006 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ (z ◇ w)) ◇ y))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ (y ◇ x))) ◇ z := by
  intro x y z
  exact (Eq.trans (h x x x x) (h ((y ◇ (z ◇ (y ◇ x))) ◇ z) x x x).symm)

/- heldout_true_007: eq4054 → eq3802 -/
theorem heldout_true_007 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ w)) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (x ◇ x) := by
  intro x y z
  exact (Eq.trans (h x y x x) (Eq.trans (h (x ◇ (x ◇ x)) x x x) (Eq.trans (h (x ◇ (x ◇ x)) (z ◇ y) x x).symm (h (z ◇ y) (x ◇ x) x x).symm)))

/- heldout_true_008: eq2123 → eq1383 -/
theorem heldout_true_008 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ x) ◇ z) ◇ (w ◇ u))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ z) ◇ x) ◇ x) := by
  intro x y z
  exact (Eq.trans (h x (x ◇ y) (x ◇ x) ((z ◇ z) ◇ x) x) (congrArg (fun t => t ◇ (((z ◇ z) ◇ x) ◇ x)) (h y x x x x).symm))

/- heldout_true_009: eq1997 → eq3701 -/
theorem heldout_true_009 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ z)) ◇ (y ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ z) ◇ (y ◇ w) := by
  intro x y z w
  exact (Eq.trans (h (x ◇ x) x x) (h ((y ◇ z) ◇ (y ◇ w)) x x).symm)

/- heldout_true_010: eq2969 → eq3469 -/
theorem heldout_true_010 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (y ◇ z)) ◇ w) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ ((y ◇ z) ◇ z) := by
  intro x y z
  exact (Eq.trans (h (x ◇ x) x x x) (h (x ◇ ((y ◇ z) ◇ z)) x x x).symm)

/- heldout_true_011: eq1795 → eq3730 -/
theorem heldout_true_011 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ y) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ y) ◇ (z ◇ w) := by
  intro x y z w
  exact (Eq.trans (h (x ◇ y) x x) (h ((x ◇ y) ◇ (z ◇ w)) x x).symm)

/- heldout_true_012: eq189 → eq3385 -/
theorem heldout_true_012 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (x ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (x ◇ (y ◇ z)) := by
  intro x y z
  have lem2 : ∀ (X Y Z : G), (X ◇ (Y ◇ Z)) = Y := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ (Y ◇ Z)) (h X x x x)) (h Y (x ◇ x) (X ◇ x) Z).symm)
  exact (Eq.trans (congrArg (fun t => x ◇ t) (lem2 (z ◇ (x ◇ (y ◇ z))) y x).symm) (lem2 x (z ◇ (x ◇ (y ◇ z))) (y ◇ x)))

/- heldout_true_013: eq2166 → eq906 -/
theorem heldout_true_013 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (y ◇ y))
    : ∀ (x : G) (y : G), x = y ◇ ((y ◇ x) ◇ (x ◇ x)) := by
  intro x y
  have lem2 : ∀ (X Y Z : G), (X ◇ ((Y ◇ Z) ◇ (Y ◇ Z))) = (Y ◇ Y) := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ ((Y ◇ Z) ◇ (Y ◇ Z))) (h X Y Z)) (h (Y ◇ Y) (Y ◇ Z) X).symm)
  exact (Eq.trans (h x (x ◇ x) x) (Eq.trans (lem2 (((x ◇ x) ◇ x) ◇ x) x x) (Eq.trans (lem2 (((x ◇ x) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ (x ◇ x)))) x x).symm (h (y ◇ ((y ◇ x) ◇ (x ◇ x))) (x ◇ x) x).symm)))

/- heldout_true_014: eq3589 → eq4511 -/
theorem heldout_true_014 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((x ◇ y) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (x ◇ y) ◇ y := by
  intro x y z
  exact (Eq.trans (congrArg (fun t => x ◇ t) (h y z ((x ◇ y) ◇ y) x)) (h (x ◇ y) y x ((y ◇ z) ◇ x)).symm)

/- heldout_true_015: eq239 → eq3014 -/
theorem heldout_true_015 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ z)) ◇ y) ◇ w := by
  intro x y z w
  exact (Eq.trans (h x x (x ◇ (x ◇ x))) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x x x).symm)) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x (((y ◇ (z ◇ z)) ◇ y) ◇ w) x))) (h (((y ◇ (z ◇ z)) ◇ y) ◇ w) x ((((y ◇ (z ◇ z)) ◇ y) ◇ w) ◇ (x ◇ x))).symm)))

/- heldout_true_016: eq992 → eq4222 -/
theorem heldout_true_016 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ z) ◇ (w ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ w) ◇ z := by
  intro x y z w
  exact (Eq.trans (h (x ◇ y) x x x) (h (((z ◇ y) ◇ w) ◇ z) x x x).symm)

/- heldout_true_017: eq613 → eq1521 -/
theorem heldout_true_017 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = y ◇ (z ◇ (w ◇ (u ◇ v))))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (x ◇ (z ◇ x)) := by
  intro x y z
  exact (Eq.trans (h x x x x x x) (h ((y ◇ y) ◇ (x ◇ (z ◇ x))) x x x x x).symm)

/- heldout_true_018: eq1959 → eq4386 -/
theorem heldout_true_018 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ (x ◇ y))
    : ∀ (x : G) (y : G), x ◇ (x ◇ x) = (y ◇ x) ◇ y := by
  intro x y
  have lem2 : ∀ (X Y Z : G), (X ◇ (Y ◇ (Y ◇ (Z ◇ X)))) = Y := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ (Y ◇ (Y ◇ (Z ◇ X)))) (h X Y Z)) (h Y (Y ◇ (Z ◇ X)) X).symm)
  have lem3 : ∀ (X Y : G), ((X ◇ Y) ◇ Y) = Y := fun X Y => (Eq.trans (congrArg (fun t => (X ◇ Y) ◇ t) (lem2 Y Y X).symm) (lem2 (X ◇ Y) Y Y))
  have lem4 : ∀ (X Y : G), (X ◇ (X ◇ (Y ◇ X))) = X := fun X Y => (Eq.trans (congrArg (fun t => t ◇ (X ◇ (Y ◇ X))) (lem3 Y X).symm) (Eq.trans (congrArg (fun t => t ◇ (X ◇ (Y ◇ X))) (congrArg (fun t => (Y ◇ X) ◇ t) (lem3 x X).symm)) (h X (Y ◇ X) (x ◇ X)).symm))
  have lem5 : ∀ (X : G), (X ◇ (X ◇ X)) = X := fun X => (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (h X (X ◇ (x ◇ X)) X)) (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (congrArg (fun t => ((X ◇ (x ◇ X)) ◇ (X ◇ X)) ◇ t) (lem4 X x))) (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (congrArg (fun t => t ◇ X) (h X X x).symm)) (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (congrArg (fun t => X ◇ t) (lem3 x X).symm)) (h X X (x ◇ X)).symm))))
  have lem6 : ∀ (X Y Z : G), ((X ◇ Y) ◇ (Z ◇ (Z ◇ X))) = Z := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ (Z ◇ (Z ◇ X))) (h (X ◇ Y) Z (Y ◇ (x ◇ X)))) (Eq.trans (congrArg (fun t => t ◇ (Z ◇ (Z ◇ X))) (congrArg (fun t => t ◇ ((X ◇ Y) ◇ Z)) (congrArg (fun t => Z ◇ t) (h X Y x).symm))) (h Z (Z ◇ X) (X ◇ Y)).symm))
  have lem7 : ∀ (X Y : G), (X ◇ (X ◇ Y)) = (X ◇ Y) := fun X Y => (Eq.trans (congrArg (fun t => X ◇ t) (lem6 X Y (X ◇ Y)).symm) (lem2 X (X ◇ Y) (X ◇ Y)))
  have lem8 : ∀ (X Y : G), ((X ◇ (X ◇ X)) ◇ (Y ◇ X)) = Y := fun X Y => (Eq.trans (congrArg (fun t => (X ◇ (X ◇ X)) ◇ t) (lem7 Y X).symm) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ (Y ◇ X))) (lem5 X)) (Eq.trans (congrArg (fun t => X ◇ t) (congrArg (fun t => Y ◇ t) (lem7 Y X).symm)) (lem2 X Y Y))))
  have lem9 : ∀ (Y X : G), (Y ◇ (Y ◇ Y)) = (X ◇ Y) := fun Y X => (Eq.trans (lem5 Y) (Eq.trans (h Y (Y ◇ (Y ◇ Y)) X) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ (Y ◇ (Y ◇ Y)))) (lem8 Y X)) (congrArg (fun t => X ◇ t) (lem4 Y Y)))))
  exact (Eq.trans (lem9 x ((y ◇ x) ◇ y)) (Eq.trans (lem6 ((y ◇ x) ◇ y) x (((y ◇ x) ◇ y) ◇ x)).symm (Eq.trans (congrArg (fun t => t ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ x) ◇ y)))) (lem9 x ((y ◇ x) ◇ y)).symm) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (congrArg (fun t => t ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ x) ◇ y))) (lem7 ((y ◇ x) ◇ y) x).symm)) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (congrArg (fun t => t ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ x) ◇ y))) (congrArg (fun t => ((y ◇ x) ◇ y) ◇ t) (lem7 ((y ◇ x) ◇ y) x).symm))) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (h (((y ◇ x) ◇ y) ◇ x) ((y ◇ x) ◇ y) ((y ◇ x) ◇ y)).symm) (lem8 x ((y ◇ x) ◇ y))))))))

/- heldout_true_019: eq800 → eq4388 -/
theorem heldout_true_019 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ ((w ◇ y) ◇ u)))
    : ∀ (x : G) (y : G), x ◇ (x ◇ x) = (y ◇ y) ◇ x := by
  intro x y
  exact (Eq.trans (h (x ◇ (x ◇ x)) x x x x) (h ((y ◇ y) ◇ x) x x x x).symm)

/- heldout_true_020: eq2966 → eq181 -/
theorem heldout_true_020 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ z)) ◇ z) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (y ◇ z) := by
  intro x y z
  exact (Eq.trans (h x x x) (h ((y ◇ y) ◇ (y ◇ z)) x x).symm)

/- heldout_true_021: eq98 → eq3482 -/
theorem heldout_true_021 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ (w ◇ u)))
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((y ◇ x) ◇ y) := by
  intro x y
  exact (Eq.trans (h (x ◇ x) x x x x) (h (y ◇ ((y ◇ x) ◇ y)) x x x x).symm)

/- heldout_true_022: eq2201 → eq1201 -/
theorem heldout_true_022 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (y ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((z ◇ (w ◇ x)) ◇ u) := by
  intro x y z w u
  exact (Eq.trans (h x x x) (h (y ◇ ((z ◇ (w ◇ x)) ◇ u)) x x).symm)

/- heldout_true_023: eq1748 → eq4204 -/
theorem heldout_true_023 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((z ◇ z) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ w) ◇ y := by
  intro x y z w
  exact (Eq.trans (h (x ◇ y) x x) (h (((z ◇ x) ◇ w) ◇ y) x x).symm)

/- heldout_true_024: eq1554 → eq2127 -/
theorem heldout_true_024 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ (x ◇ z)))
    : ∀ (x : G) (y : G), x = ((y ◇ y) ◇ x) ◇ (y ◇ x) := by
  intro x y
  have lem2 : ∀ (X Y Z : G), ((X ◇ ((Y ◇ Z) ◇ Z)) ◇ (Y ◇ Z)) = (Y ◇ Z) := fun X Y Z => (Eq.trans (congrArg (fun t => (X ◇ ((Y ◇ Z) ◇ Z)) ◇ t) (h (Y ◇ Z) Y Z)) (h (Y ◇ Z) X ((Y ◇ Z) ◇ Z)).symm)
  have lem3 : ∀ (W Y Z X : G), ((W ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) = (X ◇ ((Y ◇ Z) ◇ Z)) := fun W Y Z X => (Eq.trans (congrArg (fun t => (W ◇ (Y ◇ Z)) ◇ t) (lem2 X Y Z).symm) (Eq.trans (congrArg (fun t => (W ◇ (Y ◇ Z)) ◇ t) (congrArg (fun t => (X ◇ ((Y ◇ Z) ◇ Z)) ◇ t) (lem2 X Y Z).symm)) (h (X ◇ ((Y ◇ Z) ◇ Z)) W (Y ◇ Z)).symm))
  have lem4 : ∀ (X Y Z : G), ((X ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) = (Y ◇ Z) := fun X Y Z => (Eq.trans (lem3 X Y Z x) (Eq.trans (h (x ◇ ((Y ◇ Z) ◇ Z)) (x ◇ (Y ◇ Z)) (Y ◇ Z)) (Eq.trans (congrArg (fun t => ((x ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) ◇ t) (congrArg (fun t => (x ◇ ((Y ◇ Z) ◇ Z)) ◇ t) (lem2 x Y Z))) (Eq.trans (congrArg (fun t => ((x ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) ◇ t) (lem2 x Y Z)) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ Z)) (lem3 x Y Z x)) (lem2 x Y Z))))))
  have lem5 : ∀ (Z X Y : G), (Z ◇ (X ◇ Y)) = (X ◇ Y) := fun Z X Y => (Eq.trans (h (Z ◇ (X ◇ Y)) x (X ◇ Y)) (Eq.trans (congrArg (fun t => (x ◇ (X ◇ Y)) ◇ t) (congrArg (fun t => (Z ◇ (X ◇ Y)) ◇ t) (lem4 Z X Y))) (Eq.trans (congrArg (fun t => (x ◇ (X ◇ Y)) ◇ t) (lem4 Z X Y)) (lem4 x X Y))))
  have lem6 : ∀ (X Y Z W V : G), ((X ◇ (Y ◇ Z)) ◇ (W ◇ (Y ◇ Z))) = (V ◇ (Y ◇ Z)) := fun X Y Z W V => (Eq.trans (congrArg (fun t => t ◇ (W ◇ (Y ◇ Z))) (lem5 X Y Z)) (Eq.trans (congrArg (fun t => (Y ◇ Z) ◇ t) (lem5 W Y Z)) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ Z)) (lem2 x Y Z).symm) (Eq.trans (lem4 (x ◇ ((Y ◇ Z) ◇ Z)) Y Z) (lem5 V Y Z).symm))))
  have lem7 : ∀ (X Y Z W V U : G), ((X ◇ (Y ◇ (Z ◇ W))) ◇ (V ◇ (Z ◇ W))) = (U ◇ (Z ◇ W)) := fun X Y Z W V U => (Eq.trans (congrArg (fun t => (X ◇ (Y ◇ (Z ◇ W))) ◇ t) (lem6 U Z W x V).symm) (Eq.trans (congrArg (fun t => (X ◇ (Y ◇ (Z ◇ W))) ◇ t) (congrArg (fun t => (U ◇ (Z ◇ W)) ◇ t) (lem6 U Z W Y x).symm)) (h (U ◇ (Z ◇ W)) X (Y ◇ (Z ◇ W))).symm))
  have lem8 : ∀ (X Y Z W V : G), (X ◇ (Y ◇ (Z ◇ W))) = (V ◇ (Z ◇ W)) := fun X Y Z W V => (Eq.trans (h (X ◇ (Y ◇ (Z ◇ W))) x (x ◇ (Z ◇ W))) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ (Z ◇ W))) ◇ t) (congrArg (fun t => (X ◇ (Y ◇ (Z ◇ W))) ◇ t) (lem7 X Y Z W x x))) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ (Z ◇ W))) ◇ t) (lem7 X Y Z W x x)) (lem7 x x Z W x V))))
  exact (Eq.trans (h x x (x ◇ (y ◇ x))) (Eq.trans (congrArg (fun t => t ◇ (x ◇ (x ◇ (x ◇ (y ◇ x))))) (lem8 x x y x x)) (Eq.trans (congrArg (fun t => (x ◇ (y ◇ x)) ◇ t) (congrArg (fun t => x ◇ t) (lem8 x x y x x))) (Eq.trans (congrArg (fun t => (x ◇ (y ◇ x)) ◇ t) (lem8 x x y x x)) (lem6 x y x x ((y ◇ y) ◇ x))))))

/- heldout_true_025: eq937 → eq151 -/
theorem heldout_true_025 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((y ◇ z) ◇ (z ◇ w)))
    : ∀ (x : G), x = (x ◇ x) ◇ (x ◇ x) := by
  intro x
  exact (Eq.trans (h x x x x) (h ((x ◇ x) ◇ (x ◇ x)) x x x).symm)

/- heldout_true_026: eq1168 → eq910 -/
theorem heldout_true_026 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ y)) ◇ y))
    : ∀ (x : G) (y : G), x = y ◇ ((y ◇ x) ◇ (y ◇ y)) := by
  intro x y
  exact (Eq.trans (h x x x) (h (y ◇ ((y ◇ x) ◇ (y ◇ y))) x x).symm)

/- heldout_true_027: eq2593 → eq3990 -/
theorem heldout_true_027 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ y) ◇ z)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (x ◇ x)) ◇ z := by
  intro x y z
  exact (Eq.trans (h (x ◇ y) x x) (h ((z ◇ (x ◇ x)) ◇ z) x x).symm)

/- heldout_true_028: eq1542 → eq3064 -/
theorem heldout_true_028 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ y) ◇ (z ◇ (y ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ x) ◇ y) ◇ z) ◇ w := by
  intro x y z w
  exact (Eq.trans (h x x x x) (h ((((x ◇ x) ◇ y) ◇ z) ◇ w) x x x).symm)

/- heldout_true_029: eq1187 → eq1180 -/
theorem heldout_true_029 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ (z ◇ y)) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (z ◇ x)) ◇ x) := by
  intro x y z
  exact (Eq.trans (h x x x x) (h (y ◇ ((z ◇ (z ◇ x)) ◇ x)) x x x).symm)

/- heldout_true_030: eq3070 → eq3081 -/
theorem heldout_true_030 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ x) ◇ y) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ y) ◇ z) ◇ x := by
  intro x y z
  have lem2 : ∀ (X Y W Z : G), ((X ◇ Y) ◇ W) = ((X ◇ Y) ◇ Z) := fun X Y W Z => (Eq.trans (congrArg (fun t => t ◇ W) (congrArg (fun t => t ◇ Y) (h X Y ((X ◇ Y) ◇ X)))) (Eq.trans (h ((X ◇ Y) ◇ X) Y W).symm (Eq.trans (h ((X ◇ Y) ◇ X) Y Z) (congrArg (fun t => t ◇ Z) (congrArg (fun t => t ◇ Y) (h X Y ((X ◇ Y) ◇ X)).symm)))))
  exact (Eq.trans (h x y x) (Eq.trans (congrArg (fun t => t ◇ x) (lem2 (x ◇ y) x z y).symm) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (h (x ◇ y) x x)))) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (lem2 ((((x ◇ y) ◇ x) ◇ (x ◇ y)) ◇ x) x y x).symm)) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ y) (h (x ◇ y) x x).symm)))))))

/- heldout_true_031: eq1283 → eq631 -/
theorem heldout_true_031 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ x) ◇ z) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((x ◇ x) ◇ z)) := by
  intro x y z
  exact (Eq.trans (h x x ((((y ◇ ((x ◇ x) ◇ z)) ◇ (y ◇ ((x ◇ x) ◇ z))) ◇ x) ◇ x)) (congrArg (fun t => x ◇ t) (h (y ◇ ((x ◇ x) ◇ z)) ((x ◇ x) ◇ ((((y ◇ ((x ◇ x) ◇ z)) ◇ (y ◇ ((x ◇ x) ◇ z))) ◇ x) ◇ x)) x).symm))

/- heldout_true_032: eq2796 → eq3509 -/
theorem heldout_true_032 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (y ◇ z)) ◇ y)
    : ∀ (x : G) (y : G), x ◇ y = x ◇ ((x ◇ x) ◇ y) := by
  intro x y
  exact (Eq.trans (h (x ◇ y) x x) (h (x ◇ ((x ◇ x) ◇ y)) x x).symm)

/- heldout_true_033: eq884 → eq3474 -/
theorem heldout_true_033 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ (y ◇ z)))
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((x ◇ y) ◇ x) := by
  intro x y
  exact (Eq.trans (congrArg (fun t => x ◇ t) (h x ((y ◇ ((x ◇ y) ◇ x)) ◇ x) x)) (Eq.trans (congrArg (fun t => x ◇ t) (congrArg (fun t => ((y ◇ ((x ◇ y) ◇ x)) ◇ x) ◇ t) (h ((x ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ x)) ◇ x) ◇ x)) x x))) (h (y ◇ ((x ◇ y) ◇ x)) x ((((x ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ x)) ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x))).symm))

/- heldout_true_034: eq272 → eq3710 -/
theorem heldout_true_034 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ x) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (y ◇ z) ◇ (w ◇ u) := by
  intro x y z w u
  have lem2 : ∀ (X Y : G), (X ◇ Y) = X := fun X Y => (Eq.trans (congrArg (fun t => t ◇ Y) (h X x X)) (h X (x ◇ X) Y).symm)
  exact (Eq.trans (lem2 (x ◇ x) ((y ◇ z) ◇ (w ◇ u))).symm (Eq.trans (congrArg (fun t => t ◇ ((y ◇ z) ◇ (w ◇ u))) (lem2 (x ◇ x) ((y ◇ z) ◇ (w ◇ u))).symm) (Eq.trans (lem2 (((x ◇ x) ◇ ((y ◇ z) ◇ (w ◇ u))) ◇ ((y ◇ z) ◇ (w ◇ u))) x).symm (h ((y ◇ z) ◇ (w ◇ u)) (x ◇ x) x).symm)))

/- heldout_true_035: eq2377 → eq446 -/
theorem heldout_true_035 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (z ◇ (x ◇ x))) := by
  intro x y z
  exact (Eq.trans (h x x ((x ◇ x) ◇ (x ◇ (x ◇ x))) x) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x (x ◇ x) x x).symm)) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x ((x ◇ (y ◇ (z ◇ (x ◇ x)))) ◇ x) x x))) (h (x ◇ (y ◇ (z ◇ (x ◇ x)))) x (((x ◇ (y ◇ (z ◇ (x ◇ x)))) ◇ x) ◇ (x ◇ (x ◇ x))) x).symm)))

/- heldout_true_036: eq2057 → eq4586 -/
theorem heldout_true_036 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ x) ◇ (z ◇ y))
    : ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ x = (x ◇ y) ◇ z := by
  intro x y z
  have lem2 : ∀ (X Z Y : G), (X ◇ Z) = (X ◇ Y) := fun X Z Y => (Eq.trans (h (X ◇ Z) X x) (Eq.trans (congrArg (fun t => t ◇ (x ◇ X)) (h X Z X).symm) (Eq.trans (congrArg (fun t => t ◇ (x ◇ X)) (h X Y X)) (h (X ◇ Y) X x).symm)))
  exact (Eq.trans (congrArg (fun t => t ◇ x) (lem2 x x y)) (lem2 (x ◇ y) x z))

/- heldout_true_037: eq1367 → eq365 -/
theorem heldout_true_037 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ y) ◇ x) ◇ y))
    : ∀ (x : G) (y : G), x ◇ x = (y ◇ x) ◇ y := by
  intro x y
  have lem2 : ∀ (X Y Z : G), ((X ◇ Y) ◇ (Y ◇ (Z ◇ Y))) = Z := fun X Y Z => (Eq.trans (congrArg (fun t => (X ◇ Y) ◇ t) (congrArg (fun t => Y ◇ t) (congrArg (fun t => t ◇ Y) (h Z (X ◇ Y) x)))) (Eq.trans (congrArg (fun t => (X ◇ Y) ◇ t) (h (((x ◇ (X ◇ Y)) ◇ Z) ◇ (X ◇ Y)) Y X).symm) (h Z (X ◇ Y) x).symm))
  exact (Eq.trans (lem2 x x (x ◇ x)).symm (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (lem2 x x ((x ◇ x) ◇ x)).symm)) (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => ((x ◇ x) ◇ x) ◇ t) (h x x ((y ◇ x) ◇ y))))))) (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (lem2 (x ◇ x) x ((((y ◇ x) ◇ y) ◇ x) ◇ x)))))) (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (lem2 x x (((y ◇ x) ◇ y) ◇ x)))) (lem2 x x ((y ◇ x) ◇ y)))))))

/- heldout_true_038: eq1619 → eq809 -/
theorem heldout_true_038 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (w ◇ (w ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ ((w ◇ w) ◇ w)) := by
  intro x y z w
  exact (Eq.trans (h x x x x) (h (y ◇ (z ◇ ((w ◇ w) ◇ w))) x x x).symm)

/- heldout_true_039: eq94 → eq713 -/
theorem heldout_true_039 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (w ◇ x)))
    : ∀ (x : G) (y : G), x = y ◇ (y ◇ ((y ◇ x) ◇ x)) := by
  intro x y
  exact (h x y y (y ◇ x))

/- heldout_true_040: eq4188 → eq332 -/
theorem heldout_true_040 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ z) ◇ w) ◇ z)
    : ∀ (x : G) (y : G), x ◇ y = y ◇ (x ◇ x) := by
  intro x y
  exact (Eq.trans (h x y (x ◇ x) x) (Eq.trans (h ((y ◇ (x ◇ x)) ◇ x) (x ◇ x) x x) (h y (x ◇ x) x x).symm))

/- heldout_true_041: eq918 → eq4014 -/
theorem heldout_true_041 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((y ◇ y) ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ z)) ◇ y := by
  intro x y z
  exact (Eq.trans (h (x ◇ y) x x) (Eq.trans (congrArg (fun t => x ◇ t) (h ((x ◇ x) ◇ ((x ◇ y) ◇ x)) (x ◇ x) x)) (Eq.trans (h ((x ◇ x) ◇ (x ◇ x)) x (((x ◇ x) ◇ ((x ◇ y) ◇ x)) ◇ x)).symm (Eq.trans (h ((x ◇ x) ◇ (x ◇ x)) x (((x ◇ x) ◇ (((z ◇ (y ◇ z)) ◇ y) ◇ x)) ◇ x)) (Eq.trans (congrArg (fun t => x ◇ t) (h ((x ◇ x) ◇ (((z ◇ (y ◇ z)) ◇ y) ◇ x)) (x ◇ x) x).symm) (h ((z ◇ (y ◇ z)) ◇ y) x x).symm)))))

/- heldout_true_042: eq2209 → eq1048 -/
theorem heldout_true_042 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ z) ◇ (w ◇ z))
    : ∀ (x : G) (y : G), x = x ◇ ((y ◇ (y ◇ y)) ◇ x) := by
  intro x y
  exact (Eq.trans (h x x x x) (h (x ◇ ((y ◇ (y ◇ y)) ◇ x)) x x x).symm)

/- heldout_true_043: eq2529 → eq2327 -/
theorem heldout_true_043 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((x ◇ z) ◇ w)) ◇ u)
    : ∀ (x : G) (y : G), x = (y ◇ (y ◇ (x ◇ x))) ◇ x := by
  intro x y
  exact (Eq.trans (h x (x ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ x)) x x x) (congrArg (fun t => t ◇ x) (h (y ◇ (y ◇ (x ◇ x))) x x x ((x ◇ x) ◇ x)).symm))

/- heldout_true_044: eq599 → eq2696 -/
theorem heldout_true_044 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (w ◇ (z ◇ y))))
    : ∀ (x : G) (y : G), x = ((y ◇ x) ◇ (x ◇ x)) ◇ x := by
  intro x y
  exact (Eq.trans (h x x x x) (h (((y ◇ x) ◇ (x ◇ x)) ◇ x) x x x).symm)

/- heldout_true_045: eq3856 → eq3688 -/
theorem heldout_true_045 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ (u ◇ x))
    : ∀ (x : G) (y : G), x ◇ x = (y ◇ y) ◇ (y ◇ y) := by
  intro x y
  exact (Eq.trans (h x x (x ◇ x) (x ◇ y) x) (Eq.trans (h ((x ◇ x) ◇ (x ◇ y)) (x ◇ x) x x x) (Eq.trans (h ((x ◇ x) ◇ (x ◇ y)) (y ◇ y) x x x).symm (congrArg (fun t => t ◇ (y ◇ y)) (h y y x x x).symm))))

/- heldout_true_046: eq1622 → eq1756 -/
theorem heldout_true_046 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (w ◇ (w ◇ u)))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ x) ◇ y) := by
  intro x y z
  exact (Eq.trans (h x x x x x) (h ((y ◇ z) ◇ ((x ◇ x) ◇ y)) x x x x).symm)

/- heldout_true_047: eq3226 → eq2897 -/
theorem heldout_true_047 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ z) ◇ w) ◇ u)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ z)) ◇ w) ◇ w := by
  intro x y z w
  exact (Eq.trans (h x x x x x) (h (((x ◇ (y ◇ z)) ◇ w) ◇ w) x x x x).symm)

/- heldout_true_048: eq3251 → eq4639 -/
theorem heldout_true_048 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ w) ◇ u) ◇ u)
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (y ◇ z) ◇ y := by
  intro x y z
  exact (Eq.trans (h ((x ◇ y) ◇ x) x x x x) (h ((y ◇ z) ◇ y) x x x x).symm)

/- heldout_true_049: eq2219 → eq1221 -/
theorem heldout_true_049 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (y ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((z ◇ (w ◇ u)) ◇ u) := by
  intro x y z w u
  exact (Eq.trans (h x x x x) (h (y ◇ ((z ◇ (w ◇ u)) ◇ u)) x x x).symm)

