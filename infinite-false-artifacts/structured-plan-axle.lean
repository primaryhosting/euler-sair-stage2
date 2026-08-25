import Mathlib

class EulMagma (α : Type _) where
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => EulMagma.op

def EquationLHS (G : Type) [EulMagma G] : Prop :=
  ∀ x y : G, x = x ◇ y

def EquationRHS (G : Type) [EulMagma G] : Prop :=
  ∀ x y : G, x = y

abbrev Goal : Prop :=
  ∃ (G : Type) (_ : EulMagma G), EquationLHS G ∧ ¬ EquationRHS G

def submission : Goal := by
  let model : EulMagma Nat := ⟨fun x _ => x⟩
  refine ⟨Nat, model, ?_⟩
  constructor
  · intro x y
    rfl
  · intro goal_holds
    exact Nat.noConfusion (goal_holds 0 1)

#print axioms submission
