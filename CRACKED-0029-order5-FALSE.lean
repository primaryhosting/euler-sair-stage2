-- order5_normal_0029 FALSE: order-6 countermodel (antecedent holds 216/216, target fails 161/216), Python-verified.
-- Order-6 certificate for the judge-controlled Goal. Exact 4.33.1 gate remains to be run.

import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
import JudgeProblem
open MemoFinOp
set_option maxRecDepth 8000 in
def submission : Goal := by
  let m : Magma (Fin 6) := { op := finOpTable "[[1, 2, 0, 0, 0, 0], [1, 3, 1, 2, 1, 1], [1, 3, 2, 2, 0, 2], [1, 3, 3, 4, 5, 3], [2, 4, 4, 4, 0, 4], [1, 5, 5, 4, 2, 5]]" }
  refine ⟨Fin 6, m, ?_⟩
  decideFin!
