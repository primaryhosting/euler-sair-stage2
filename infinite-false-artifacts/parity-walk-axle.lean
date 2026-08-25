import Mathlib

class EulMagma (α : Type _) where
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => EulMagma.op

def EquationLHS (G : Type) [EulMagma G] : Prop :=
  ∀ x y z : G, x = y ◇ ((z ◇ (y ◇ y)) ◇ x)

def EquationRHS (G : Type) [EulMagma G] : Prop :=
  ∀ x y : G, x = y

abbrev Goal : Prop :=
  ∃ (G : Type) (_ : EulMagma G), EquationLHS G ∧ ¬ EquationRHS G

def submission : Goal := by
  let op : (Bool × Nat) → (Bool × Nat) → (Bool × Nat) :=
    fun a x =>
      match a.1, x.1 with
      | false, q => (Bool.not q, x.2)
      | true, false =>
          Nat.rec (false, Nat.zero) (fun k _ => (true, k)) x.2
      | true, true => (false, Nat.succ x.2)
  let model : EulMagma (Bool × Nat) := ⟨op⟩
  refine ⟨Bool × Nat, model, ?_⟩
  constructor
  · intro v0 v1 v2
    change v0 = op v1 (op (op v2 (op v1 v1)) v0)
    have left_congr (a b x : Bool × Nat) (hab : a.1 = b.1) :
        op a x = op b x := by
      cases a with
      | mk qa ka =>
        cases b with
        | mk qb kb =>
          cases x with
          | mk qx kx =>
            cases hab
            rfl
    have invol (a x : Bool × Nat) : op a (op a x) = x := by
      cases a with
      | mk qa ka =>
        cases x with
        | mk qx kx =>
          cases qa
          · cases qx <;> rfl
          · cases qx
            · exact Nat.rec (by rfl) (fun k _ => by rfl) kx
            · rfl
    have middle (z y : Bool × Nat) : (op z (op y y)).1 = y.1 := by
      cases z with
      | mk qz kz =>
        cases y with
        | mk qy ky =>
          cases qz <;> cases qy <;> rfl
    rw [left_congr (op v2 (op v1 v1)) v1 v0 (middle v2 v1)]
    exact (invol v1 v0).symm
  · intro goal_holds
    have bad := goal_holds (false, Nat.zero) (true, Nat.zero)
    change (false, Nat.zero) = (true, Nat.zero) at bad
    exact Bool.noConfusion (congrArg Prod.fst bad)

#print axioms submission
