-- Proof archive: Aristotle-proved and AXLE-verified on lean-4.33.0.
-- Use the separate SUBMISSION files for the judge; official 4.33.1 gate is pending.

class Magma (G : Type _) where op : G → G → G
@[inherit_doc] infixl:65 " ◇ " => Magma.op
export Magma (op)



-- order5_normal_0030 (collapse; independently matching-reconstructed from E as well)
/-- From `h` the magma collapses: every two elements are equal (see `e29` below),
which immediately gives the goal. -/
theorem problem_0030 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ z) ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ (z ◇ (z ◇ y))) ◇ w) := by
  have e0 : ∀ a b c d : G, ((a ◇ (b ◇ c)) ◇ ((((d ◇ d) ◇ (c ◇ d)) ◇ ((d ◇ d) ◇ (c ◇ d))) ◇ c)) = (b ◇ c) := fun a b c d => Eq.trans (congrArg (fun t : G => ((a ◇ (b ◇ c)) ◇ ((((d ◇ d) ◇ (c ◇ d)) ◇ ((d ◇ d) ◇ (c ◇ d))) ◇ t))) (h c b d)) (h (b ◇ c) a ((d ◇ d) ◇ (c ◇ d))).symm
  have e1 : ∀ a b c : G, (a ◇ ((b ◇ b) ◇ (((c ◇ c) ◇ (a ◇ c)) ◇ b))) = ((c ◇ c) ◇ (a ◇ c)) := fun a b c => Eq.trans (congrArg (fun t : G => (t ◇ ((b ◇ b) ◇ (((c ◇ c) ◇ (a ◇ c)) ◇ b)))) (h a a c)) (h ((c ◇ c) ◇ (a ◇ c)) (a ◇ a) b).symm
  have e2 : ∀ a b c d : G, ((a ◇ b) ◇ ((((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c))) ◇ b)) = ((((d ◇ d) ◇ (b ◇ d)) ◇ ((d ◇ d) ◇ (b ◇ d))) ◇ b) := fun a b c d => Eq.trans (congrArg (fun t : G => (t ◇ ((((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c))) ◇ b))) (e0 a a b d).symm) (e0 (a ◇ (a ◇ b)) (((d ◇ d) ◇ (b ◇ d)) ◇ ((d ◇ d) ◇ (b ◇ d))) b c)
  have e3 : ∀ a b c : G, ((((a ◇ a) ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ (b ◇ a))) ◇ b) = ((((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c))) ◇ b) := fun a b c => Eq.trans ((e2 a b a a).symm) (e2 a b a c)
  have e4 : ∀ a b c : G, (a ◇ ((((b ◇ b) ◇ ((a ◇ c) ◇ b)) ◇ ((b ◇ b) ◇ ((a ◇ c) ◇ b))) ◇ (a ◇ c))) = ((c ◇ c) ◇ (a ◇ c)) := fun a b c => Eq.trans (congrArg (fun t : G => (a ◇ ((((b ◇ b) ◇ ((a ◇ c) ◇ b)) ◇ ((b ◇ b) ◇ ((a ◇ c) ◇ b))) ◇ t))) (h (a ◇ c) (c ◇ c) b)) (e1 a ((b ◇ b) ◇ ((a ◇ c) ◇ b)) c)
  have e5 : ∀ a b c d e : G, ((a ◇ (b ◇ c)) ◇ ((d ◇ c) ◇ ((((e ◇ e) ◇ (c ◇ e)) ◇ ((e ◇ e) ◇ (c ◇ e))) ◇ c))) = (b ◇ c) := fun a b c d e => Eq.trans (congrArg (fun t : G => ((a ◇ (b ◇ c)) ◇ t)) (e2 d c e a)) (e0 a b c a)
  have e6 : ∀ a b : G, ((a ◇ a) ◇ ((((b ◇ b) ◇ (a ◇ b)) ◇ ((b ◇ b) ◇ (a ◇ b))) ◇ a)) = (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) := fun a b => Eq.trans (congrArg (fun t : G => ((a ◇ a) ◇ t)) (e2 a a a b).symm) (e1 (a ◇ a) a (a ◇ a))
  have e7 : ∀ a b : G, (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) = ((((b ◇ b) ◇ (a ◇ b)) ◇ ((b ◇ b) ◇ (a ◇ b))) ◇ a) := fun a b => Eq.trans ((e6 a a).symm) (e2 a a a b)
  have e8 : ∀ a b c d : G, ((a ◇ (b ◇ c)) ◇ ((d ◇ c) ◇ (((c ◇ c) ◇ (c ◇ c)) ◇ ((c ◇ c) ◇ (c ◇ c))))) = (b ◇ c) := fun a b c d => Eq.trans (congrArg (fun t : G => ((a ◇ (b ◇ c)) ◇ ((d ◇ c) ◇ t))) (e7 c a)) (e5 a b c d a)
  have e9 : ∀ a b c d : G, ((a ◇ b) ◇ ((((c ◇ c) ◇ (((d ◇ d) ◇ (b ◇ d)) ◇ c)) ◇ ((c ◇ c) ◇ (((d ◇ d) ◇ (b ◇ d)) ◇ c))) ◇ ((d ◇ d) ◇ (b ◇ d)))) = b := fun a b c d => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ ((((c ◇ c) ◇ (((d ◇ d) ◇ (b ◇ d)) ◇ c)) ◇ ((c ◇ c) ◇ (((d ◇ d) ◇ (b ◇ d)) ◇ c))) ◇ t))) (e1 b c d).symm) (h b a ((c ◇ c) ◇ (((d ◇ d) ◇ (b ◇ d)) ◇ c))).symm
  have e10 : ∀ a b c : G, ((a ◇ b) ◇ (((((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c))) ◇ (((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c)))) ◇ ((((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c))) ◇ (((c ◇ c) ◇ (b ◇ c)) ◇ ((c ◇ c) ◇ (b ◇ c)))))) = b := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ t)) (e7 ((c ◇ c) ◇ (b ◇ c)) a)) (e9 a b a c)
  have e11 : ∀ a : G, a = (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) := fun a => Eq.trans ((e10 a a a).symm) (e1 (a ◇ a) (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) (a ◇ a))
  have e12 : ∀ a b c : G, ((a ◇ (b ◇ c)) ◇ (((c ◇ c) ◇ (c ◇ c)) ◇ ((c ◇ c) ◇ (c ◇ c)))) = (b ◇ c) := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ (b ◇ c)) ◇ t)) (e7 c a)) (e0 a b c a)
  have e13 : ∀ a b c : G, ((a ◇ (b ◇ c)) ◇ c) = (b ◇ c) := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ (b ◇ c)) ◇ t)) (e11 c)) (e12 a b c)
  have e14 : ∀ a b : G, (a ◇ (a ◇ b)) = ((b ◇ b) ◇ (a ◇ b)) := fun a b => Eq.trans (congrArg (fun t : G => (t ◇ (a ◇ b))) (h a a b)) (e13 (a ◇ a) (b ◇ b) (a ◇ b))
  have e15 : ∀ a b c : G, ((a ◇ b) ◇ (b ◇ (b ◇ c))) = b := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ t)) (e14 b c)) (h b a c).symm
  have e16 : ∀ a b c : G, ((a ◇ b) ◇ ((c ◇ (c ◇ c)) ◇ (b ◇ (c ◇ c)))) = b := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ (t ◇ (b ◇ (c ◇ c))))) (e14 c c)) (h b a (c ◇ c)).symm
  have e17 : ∀ a b c : G, ((a ◇ b) ◇ (c ◇ (b ◇ ((c ◇ c) ◇ (c ◇ c))))) = b := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ (t ◇ (b ◇ ((c ◇ c) ◇ (c ◇ c)))))) (h c c c)) (e16 a b (c ◇ c))
  have e18 : ∀ a b c : G, ((a ◇ b) ◇ (c ◇ (b ◇ (c ◇ (c ◇ c))))) = b := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ (c ◇ (b ◇ t)))) (e14 c c)) (e17 a b c)
  have e19 : ∀ a b c : G, ((a ◇ (b ◇ c)) ◇ (c ◇ c)) = (b ◇ c) := fun a b c => Eq.trans (congrArg (fun t : G => ((a ◇ (b ◇ c)) ◇ (c ◇ t))) (e15 b c c).symm) (e18 a (b ◇ c) c)
  have e20 : ∀ a b : G, ((a ◇ b) ◇ (b ◇ b)) = (b ◇ b) := fun a b => Eq.trans (congrArg (fun t : G => (t ◇ (b ◇ b))) (e19 a a b).symm) (e19 (a ◇ (a ◇ b)) b b)
  have e21 : ∀ a b : G, ((a ◇ b) ◇ (b ◇ b)) = b := fun a b => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ t)) (e20 b b).symm) (h b a b).symm
  have e22 : ∀ a : G, (a ◇ a) = a := fun a => Eq.trans ((e20 a a).symm) (e21 a a)
  have e23 : ∀ a b : G, ((a ◇ b) ◇ b) = (b ◇ b) := fun a b => Eq.trans (congrArg (fun t : G => (t ◇ b)) (e19 a a b).symm) (e13 (a ◇ (a ◇ b)) b b)
  have e24 : ∀ a b : G, ((a ◇ b) ◇ b) = (a ◇ b) := fun a b => Eq.trans (congrArg (fun t : G => (t ◇ b)) (e22 (a ◇ b)).symm) (e13 (a ◇ b) a b)
  have e25 : ∀ a b : G, (a ◇ a) = (b ◇ a) := fun a b => Eq.trans ((e23 b a).symm) (e24 b a)
  have e26 : ∀ a b : G, a = (b ◇ a) := fun a b => Eq.trans ((e22 a).symm) (e25 a b)
  have e27 : ∀ a b : G, (a ◇ (a ◇ b)) = a := fun a b => Eq.trans ((e26 (a ◇ (a ◇ b)) (a ◇ a))) (e15 a a b)
  have e28 : ∀ a b : G, (a ◇ b) = a := fun a b => Eq.trans ((e26 (a ◇ b) a)) (e27 a b)
  have e29 : ∀ a b : G, a = b := fun a b => Eq.trans ((e26 a b)) (e28 b a)
  intro x y z w
  exact e29 x (y ◇ ((x ◇ (z ◇ (z ◇ y))) ◇ w))

-- order5_normal_0036 (control; already cracked via eprover -> right-absorption)
/-- From `h` one derives the right-absorption law `a ◇ b = a` (see `L10` below),
from which the goal is immediate. -/
theorem problem_0036 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((y ◇ x) ◇ (y ◇ z))))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ (y ◇ (z ◇ (w ◇ u)))) ◇ z := by
  have L0 : ∀ a b c : G, a = (a ◇ (b ◇ ((b ◇ a) ◇ (b ◇ c)))) := h
  have L1 : ∀ a b : G, (a ◇ (b ◇ (b ◇ a))) = a := fun a b => Eq.trans (congrArg (fun t : G => (a ◇ (b ◇ t))) (L0 (b ◇ a) b a)) (L0 a b ((b ◇ (b ◇ a)) ◇ (b ◇ a))).symm
  have L2 : ∀ a : G, ((a ◇ a) ◇ a) = (a ◇ a) := fun a => Eq.trans (congrArg (fun t : G => ((a ◇ a) ◇ t)) (L1 a a).symm) (L1 (a ◇ a) a)
  have L3 : ∀ a b : G, (a ◇ (b ◇ ((b ◇ a) ◇ ((b ◇ b) ◇ b)))) = a := fun a b => Eq.trans (congrArg (fun t : G => (a ◇ (b ◇ ((b ◇ a) ◇ t)))) (L2 b)) (L0 a b b).symm
  have L4 : ∀ a : G, (a ◇ a) = a := fun a => Eq.trans (congrArg (fun t : G => (a ◇ t)) (L1 a (a ◇ a)).symm) (L3 a a)
  have L5 : ∀ a b : G, (a ◇ (a ◇ (a ◇ (a ◇ b)))) = a := fun a b => Eq.trans (congrArg (fun t : G => (a ◇ (a ◇ (t ◇ (a ◇ b))))) (L4 a).symm) (L0 a a b).symm
  have L6 : ∀ a b : G, ((a ◇ (a ◇ b)) ◇ a) = (a ◇ (a ◇ b)) := fun a b => Eq.trans (congrArg (fun t : G => ((a ◇ (a ◇ b)) ◇ t)) (L5 a b).symm) (L1 (a ◇ (a ◇ b)) a)
  have L7 : ∀ a b : G, (a ◇ ((a ◇ (a ◇ b)) ◇ (a ◇ (a ◇ b)))) = a := fun a b => Eq.trans (congrArg (fun t : G => (a ◇ ((a ◇ (a ◇ b)) ◇ t))) (L6 a b).symm) (L1 a (a ◇ (a ◇ b)))
  have L8 : ∀ a b : G, ((a ◇ b) ◇ a) = (a ◇ b) := fun a b => Eq.trans (congrArg (fun t : G => ((a ◇ b) ◇ t)) (L7 a b).symm) (L0 (a ◇ b) a (a ◇ b)).symm
  have L9 : ∀ a b c : G, (a ◇ (b ◇ ((b ◇ a) ◇ ((b ◇ c) ◇ b)))) = a := fun a b c => Eq.trans (congrArg (fun t : G => (a ◇ (b ◇ ((b ◇ a) ◇ t)))) (L8 b c)) (L0 a b c).symm
  have L10 : ∀ a b : G, (a ◇ b) = a := fun a b => Eq.trans (congrArg (fun t : G => (a ◇ t)) (L1 b (b ◇ a)).symm) (L9 a b a)
  intro x y z w u
  exact ((L10 (x ◇ (y ◇ (z ◇ (w ◇ u)))) z).trans (L10 x (y ◇ (z ◇ (w ◇ u))))).symm
