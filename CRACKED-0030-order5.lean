-- order5_normal_0030 : x = (y ◇ x) ◇ ((z ◇ z) ◇ (x ◇ z))  =>  x = y ◇ ((x ◇ (z ◇ (z ◇ y))) ◇ w)
-- Matching-reconstructed E proof archive; AXLE-verified on lean-4.33.0.
-- Derives universal collapse. Official judge 4.33.1 gate is pending.

class Magma (α : Type _) where op : α → α → α
@[inherit_doc] infix:65 " ◇ " => Magma.op
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ z) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ (z ◇ (z ◇ y))) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
def submission : Goal := by
  intro G _ h
  have d0 : ∀ (X6 : G) (X5 : G) (X7 : G), X5 = ((X6 ◇ X5) ◇ ((X7 ◇ X7) ◇ (X5 ◇ X7))) := fun X6 X5 X7 => (h X5 X6 X7)
  have d1 : ∀ (X2 : G) (X1 : G) (X3 : G), X1 = ((X2 ◇ X1) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) := fun X2 X1 X3 => (d0 X2 X1 X3)
  have d2 : ∀ (v0 : G) (v1 : G) (v2 : G) (v3 : G), ((v2 ◇ (v0 ◇ v1)) ◇ ((((v3 ◇ v3) ◇ (v1 ◇ v3)) ◇ ((v3 ◇ v3) ◇ (v1 ◇ v3))) ◇ v1)) = (v0 ◇ v1) := fun v0 v1 v2 v3 => ((congrArg (fun t => (v2 ◇ (v0 ◇ v1)) ◇ t) (congrArg (fun t => (((v3 ◇ v3) ◇ (v1 ◇ v3)) ◇ ((v3 ◇ v3) ◇ (v1 ◇ v3))) ◇ t) (((d1 v0 v1 v3)).symm))).symm.trans (((d1 v2 (v0 ◇ v1) ((v3 ◇ v3) ◇ (v1 ◇ v3)))).symm))
  have d3 : ∀ (X2 : G) (X3 : G) (X1 : G) (X4 : G), ((X1 ◇ (X2 ◇ X3)) ◇ ((((X4 ◇ X4) ◇ (X3 ◇ X4)) ◇ ((X4 ◇ X4) ◇ (X3 ◇ X4))) ◇ X3)) = (X2 ◇ X3) := fun X2 X3 X1 X4 => (d2 X2 X3 X1 X4)
  have d4 : ∀ (v0 : G) (v1 : G) (v2 : G), (v1 ◇ ((v2 ◇ v2) ◇ (((v0 ◇ v0) ◇ (v1 ◇ v0)) ◇ v2))) = ((v0 ◇ v0) ◇ (v1 ◇ v0)) := fun v0 v1 v2 => ((congrArg (fun t => t ◇ ((v2 ◇ v2) ◇ (((v0 ◇ v0) ◇ (v1 ◇ v0)) ◇ v2))) (((d1 v0 v1 v0)).symm)).symm.trans (((d1 (v0 ◇ v1) ((v0 ◇ v0) ◇ (v1 ◇ v0)) v2)).symm))
  have d5 : ∀ (X3 : G) (X1 : G) (X2 : G), (X1 ◇ ((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ X2))) = ((X3 ◇ X3) ◇ (X1 ◇ X3)) := fun X3 X1 X2 => (d4 X3 X1 X2)
  have d6 : ∀ (v0 : G) (v1 : G) (v2 : G) (v3 : G), ((v2 ◇ v1) ◇ ((((v3 ◇ v3) ◇ (v1 ◇ v3)) ◇ ((v3 ◇ v3) ◇ (v1 ◇ v3))) ◇ v1)) = ((((v0 ◇ v0) ◇ (v1 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v1 ◇ v0))) ◇ v1) := fun v0 v1 v2 v3 => ((congrArg (fun t => t ◇ ((((v3 ◇ v3) ◇ (v1 ◇ v3)) ◇ ((v3 ◇ v3) ◇ (v1 ◇ v3))) ◇ v1)) ((d3 v2 v1 v0 v0))).symm.trans ((d3 (((v0 ◇ v0) ◇ (v1 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v1 ◇ v0))) v1 (v0 ◇ (v2 ◇ v1)) v3)))
  have d7 : ∀ (X4 : G) (X2 : G) (X1 : G) (X3 : G), ((X1 ◇ X2) ◇ ((((X3 ◇ X3) ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X3))) ◇ X2)) = ((((X4 ◇ X4) ◇ (X2 ◇ X4)) ◇ ((X4 ◇ X4) ◇ (X2 ◇ X4))) ◇ X2) := fun X4 X2 X1 X3 => (d6 X4 X2 X1 X3)
  have d8 : ∀ (v0 : G) (v1 : G) (v2 : G) (v3 : G) (v4 : G), ((v2 ◇ (v0 ◇ v1)) ◇ ((v3 ◇ v1) ◇ ((((v4 ◇ v4) ◇ (v1 ◇ v4)) ◇ ((v4 ◇ v4) ◇ (v1 ◇ v4))) ◇ v1))) = (v0 ◇ v1) := fun v0 v1 v2 v3 v4 => ((congrArg (fun t => (v2 ◇ (v0 ◇ v1)) ◇ t) (((d7 v0 v1 v3 v4)).symm)).symm.trans ((d3 v0 v1 v2 v0)))
  have d9 : ∀ (X2 : G) (X3 : G) (X1 : G) (X4 : G) (X5 : G), ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ ((((X5 ◇ X5) ◇ (X3 ◇ X5)) ◇ ((X5 ◇ X5) ◇ (X3 ◇ X5))) ◇ X3))) = (X2 ◇ X3) := fun X2 X3 X1 X4 X5 => (d8 X2 X3 X1 X4 X5)
  have d10 : ∀ (v0 : G) (v1 : G) (v2 : G) (v3 : G) (v4 : G) (v5 : G), ((v2 ◇ (v0 ◇ v1)) ◇ ((v3 ◇ v1) ◇ ((v4 ◇ v1) ◇ ((((v5 ◇ v5) ◇ (v1 ◇ v5)) ◇ ((v5 ◇ v5) ◇ (v1 ◇ v5))) ◇ v1)))) = (v0 ◇ v1) := fun v0 v1 v2 v3 v4 v5 => ((congrArg (fun t => (v2 ◇ (v0 ◇ v1)) ◇ t) (congrArg (fun t => (v3 ◇ v1) ◇ t) (((d7 v0 v1 v4 v5)).symm))).symm.trans ((d9 v0 v1 v2 v3 v0)))
  have d11 : ∀ (X2 : G) (X3 : G) (X1 : G) (X4 : G) (X5 : G) (X6 : G), ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ ((X5 ◇ X3) ◇ ((((X6 ◇ X6) ◇ (X3 ◇ X6)) ◇ ((X6 ◇ X6) ◇ (X3 ◇ X6))) ◇ X3)))) = (X2 ◇ X3) := fun X2 X3 X1 X4 X5 X6 => (d10 X2 X3 X1 X4 X5 X6)
  have d12 : ∀ (v0 : G) (v1 : G) (v2 : G), ((v2 ◇ (v0 ◇ v1)) ◇ (((v1 ◇ v1) ◇ (v1 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v1 ◇ v1)))) = (v0 ◇ v1) := fun v0 v1 v2 => ((congrArg (fun t => (v2 ◇ (v0 ◇ v1)) ◇ t) ((d5 (v1 ◇ v1) (v1 ◇ v1) v1))).symm.trans ((d11 v0 v1 v2 v1 v1 v1)))
  have d13 : ∀ (X2 : G) (X3 : G) (X1 : G), ((X1 ◇ (X2 ◇ X3)) ◇ (((X3 ◇ X3) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) = (X2 ◇ X3) := fun X2 X3 X1 => (d12 X2 X3 X1)
  have d14 : ∀ (v0 : G) (v1 : G) (v2 : G) (v3 : G), (((v1 ◇ v0) ◇ ((((v2 ◇ v2) ◇ (v0 ◇ v2)) ◇ ((v2 ◇ v2) ◇ (v0 ◇ v2))) ◇ v0)) ◇ ((v3 ◇ v3) ◇ (v0 ◇ v3))) = v0 := fun v0 v1 v2 v3 => ((congrArg (fun t => t ◇ ((v3 ◇ v3) ◇ (v0 ◇ v3))) (((d7 v0 v0 v1 v2)).symm)).symm.trans (((d1 (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) v0 v3)).symm))
  have d15 : ∀ (X2 : G) (X1 : G) (X3 : G) (X4 : G), (((X1 ◇ X2) ◇ ((((X3 ◇ X3) ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X3))) ◇ X2)) ◇ ((X4 ◇ X4) ◇ (X2 ◇ X4))) = X2 := fun X2 X1 X3 X4 => (d14 X2 X1 X3 X4)
  have d16 : ∀ (v0 : G) (v1 : G) (v2 : G) (v3 : G) (v4 : G), (((v1 ◇ v0) ◇ ((v2 ◇ v0) ◇ ((((v3 ◇ v3) ◇ (v0 ◇ v3)) ◇ ((v3 ◇ v3) ◇ (v0 ◇ v3))) ◇ v0))) ◇ ((v4 ◇ v4) ◇ (v0 ◇ v4))) = v0 := fun v0 v1 v2 v3 v4 => ((congrArg (fun t => t ◇ ((v4 ◇ v4) ◇ (v0 ◇ v4))) (congrArg (fun t => (v1 ◇ v0) ◇ t) (((d7 v0 v0 v2 v3)).symm))).symm.trans ((d15 v0 v1 v0 v4)))
  have d17 : ∀ (X2 : G) (X1 : G) (X3 : G) (X4 : G) (X5 : G), (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ ((((X4 ◇ X4) ◇ (X2 ◇ X4)) ◇ ((X4 ◇ X4) ◇ (X2 ◇ X4))) ◇ X2))) ◇ ((X5 ◇ X5) ◇ (X2 ◇ X5))) = X2 := fun X2 X1 X3 X4 X5 => (d16 X2 X1 X3 X4 X5)
  have d18 : ∀ (v0 : G) (v1 : G), ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) = v0 := fun v0 v1 => ((congrArg (fun t => t ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ((d5 (v0 ◇ v0) (v0 ◇ v0) v0))).symm.trans ((d17 v0 v0 v0 v0 v1)))
  have d19 : ∀ (X1 : G) (X2 : G), ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) = X1 := fun X1 X2 => (d18 X1 X2)
  have d20 : ∀ (v0 : G) (v1 : G) (v2 : G), (v1 ◇ ((((v2 ◇ v2) ◇ ((v1 ◇ v0) ◇ v2)) ◇ ((v2 ◇ v2) ◇ ((v1 ◇ v0) ◇ v2))) ◇ (v1 ◇ v0))) = ((v0 ◇ v0) ◇ (v1 ◇ v0)) := fun v0 v1 v2 => ((congrArg (fun t => v1 ◇ t) (congrArg (fun t => (((v2 ◇ v2) ◇ ((v1 ◇ v0) ◇ v2)) ◇ ((v2 ◇ v2) ◇ ((v1 ◇ v0) ◇ v2))) ◇ t) (((d1 (v0 ◇ v0) (v1 ◇ v0) v2)).symm))).symm.trans ((d5 v0 v1 ((v2 ◇ v2) ◇ ((v1 ◇ v0) ◇ v2)))))
  have d21 : ∀ (X3 : G) (X1 : G) (X2 : G), (X1 ◇ ((((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2))) ◇ (X1 ◇ X3))) = ((X3 ◇ X3) ◇ (X1 ◇ X3)) := fun X3 X1 X2 => (d20 X3 X1 X2)
  have d22 : ∀ (v0 : G) (v1 : G), (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((((((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ◇ ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1)))) ◇ ((((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ◇ v0)) ◇ (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))))) = ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) := fun v0 v1 => ((congrArg (fun t => ((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ t) (congrArg (fun t => t ◇ (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) (congrArg (fun t => ((((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ◇ ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1)))) ◇ t) (congrArg (fun t => (((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ◇ t) ((d19 v0 v1)))))).symm.trans ((d21 ((v0 ◇ v0) ◇ (v0 ◇ v0)) ((v0 ◇ v0) ◇ (v0 ◇ v0)) ((v1 ◇ v1) ◇ (v0 ◇ v1)))))
  have d23 : ∀ (v0 : G) (v1 : G), (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ◇ v0)) = ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) := fun v0 v1 => ((congrArg (fun t => ((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ t) ((d13 (((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) v0 ((((v1 ◇ v1) ◇ (v0 ◇ v1)) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ◇ ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))))))).symm.trans ((d22 v0 v1)))
  have d24 : ∀ (v0 : G), (v0 ◇ v0) = ((((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) := fun v0 => (((d3 v0 v0 (v0 ◇ v0) v0)).symm.trans ((d23 v0 v0)))
  have d25 : ∀ (X1 : G), ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = (X1 ◇ X1) := fun X1 => ((d24 X1)).symm
  have d26 : ∀ (v0 : G), (v0 ◇ (v0 ◇ v0)) = ((v0 ◇ v0) ◇ (v0 ◇ v0)) := fun v0 => ((congrArg (fun t => v0 ◇ t) ((d25 v0))).symm.trans ((d5 v0 v0 ((v0 ◇ v0) ◇ (v0 ◇ v0)))))
  have d27 : ∀ (X1 : G), ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := fun X1 => ((d26 X1)).symm
  have d28 : ∀ (v0 : G) (v1 : G), (((v0 ◇ v0) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) = v0 := fun v0 v1 => ((congrArg (fun t => t ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) ((d27 (v0 ◇ v0)))).symm.trans ((d19 v0 v1)))
  have d29 : ∀ (v0 : G) (v1 : G), (v0 ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) = v0 := fun v0 v1 => ((congrArg (fun t => t ◇ ((v1 ◇ v1) ◇ (v0 ◇ v1))) (((d1 v0 v0 v0)).symm)).symm.trans ((d28 v0 v1)))
  have d30 : ∀ (X1 : G) (X2 : G), (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) = X1 := fun X1 X2 => (d29 X1 X2)
  have d31 : ∀ (v0 : G), (v0 ◇ (v0 ◇ (v0 ◇ v0))) = v0 := fun v0 => ((congrArg (fun t => v0 ◇ t) ((d27 v0))).symm.trans ((d30 v0 v0)))
  have d32 : ∀ (X1 : G), (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := fun X1 => (d31 X1)
  have d33 : ∀ (v0 : G), ((v0 ◇ v0) ◇ v0) = (v0 ◇ v0) := fun v0 => ((congrArg (fun t => (v0 ◇ v0) ◇ t) (((d1 v0 v0 v0)).symm)).symm.trans ((d32 (v0 ◇ v0))))
  have d34 : ∀ (X1 : G), ((X1 ◇ X1) ◇ X1) = (X1 ◇ X1) := fun X1 => (d33 X1)
  have d35 : ∀ (v0 : G), ((v0 ◇ v0) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0))) = (v0 ◇ v0) := fun v0 => ((congrArg (fun t => (v0 ◇ v0) ◇ t) (congrArg (fun t => (v0 ◇ v0) ◇ t) ((d34 v0)))).symm.trans ((d30 (v0 ◇ v0) v0)))
  have d36 : ∀ (v0 : G), v0 = (v0 ◇ v0) := fun v0 => ((((d1 v0 v0 v0)).symm).symm.trans ((d35 v0)))
  have d37 : ∀ (X1 : G), (X1 ◇ X1) = X1 := fun X1 => ((d36 X1)).symm
  have d38 : ∀ (v0 : G) (v1 : G), ((v1 ◇ v0) ◇ (v0 ◇ v0)) = v0 := fun v0 v1 => ((congrArg (fun t => (v1 ◇ v0) ◇ t) ((d37 (v0 ◇ v0)))).symm.trans (((d1 v1 v0 v0)).symm))
  have d39 : ∀ (v0 : G) (v1 : G), ((v1 ◇ v0) ◇ v0) = v0 := fun v0 v1 => ((congrArg (fun t => (v1 ◇ v0) ◇ t) ((d37 v0))).symm.trans ((d38 v0 v1)))
  have d40 : ∀ (X2 : G) (X1 : G), ((X1 ◇ X2) ◇ X2) = X2 := fun X2 X1 => (d39 X2 X1)
  have d41 : ∀ (v0 : G) (v1 : G), ((v0 ◇ v1) ◇ ((v1 ◇ v1) ◇ v1)) = (v0 ◇ v1) := fun v0 v1 => ((congrArg (fun t => (v0 ◇ v1) ◇ t) (congrArg (fun t => (v1 ◇ v1) ◇ t) ((d40 v1 v0)))).symm.trans ((d30 (v0 ◇ v1) v1)))
  have d42 : ∀ (v0 : G) (v1 : G), ((v0 ◇ v1) ◇ v1) = (v0 ◇ v1) := fun v0 v1 => ((congrArg (fun t => (v0 ◇ v1) ◇ t) ((d40 v1 v1))).symm.trans ((d41 v0 v1)))
  have d43 : ∀ (v0 : G) (v1 : G), v1 = (v0 ◇ v1) := fun v0 v1 => (((d40 v1 v0)).symm.trans ((d42 v0 v1)))
  have d44 : ∀ (X2 : G) (X1 : G), (X1 ◇ X2) = X2 := fun X2 X1 => ((d43 X1 X2)).symm
  have d45 : ∀ (v0 : G) (v1 : G), ((v1 ◇ v1) ◇ (v0 ◇ v1)) = v0 := fun v0 v1 => (((d44 ((v1 ◇ v1) ◇ (v0 ◇ v1)) v0)).symm.trans ((d30 v0 v1)))
  have d46 : ∀ (v0 : G) (v1 : G), (v0 ◇ v1) = v0 := fun v0 v1 => (((d44 (v0 ◇ v1) (v1 ◇ v1))).symm.trans ((d45 v0 v1)))
  have d47 : ∀ (v0 : G) (v1 : G), v1 = v0 := fun v0 v1 => (((d44 v1 v0)).symm.trans ((d46 v0 v1)))
  have d48 : ∀ (X2 : G) (X1 : G), X1 = X2 := fun X2 X1 => (d47 X2 X1)
  intro x y z w
  exact ((d48 x x)).symm.trans ((d48 (y ◇ ((x ◇ (z ◇ (z ◇ y))) ◇ w)) x))
