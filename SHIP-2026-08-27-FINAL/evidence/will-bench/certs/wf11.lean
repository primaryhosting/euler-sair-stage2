import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

set_option maxRecDepth 8000 in
def submission : Goal := by
  let m : Magma (Fin 2) := {
    op := finOpTable "[[0, 1], [0, 1]]"
  }
  refine ⟨Fin 2, m, ?_⟩
  decideFin!
