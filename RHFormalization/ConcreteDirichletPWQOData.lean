import RHFormalization.DirichletPWQOModel
import RHFormalization.DirichletLaplacianEigenpairs

namespace RHFormalization

noncomputable section

open Real

def concreteDirichletPWQOData : DirichletPWQOData where
  L := 1
  L_pos := one_pos
  lamShifted := fun n => ((n : ℝ) * Real.pi) ^ 2
  nonneg := fun n => by positivity
  growth := by
    intro n
    have h2 : (2 : ℝ) * 1 = 2 := by norm_num
    rw [h2]
    have hsq : ((n : ℝ) * Real.pi / 2) ^ 2 = (1/4) * ((n : ℝ) * Real.pi) ^ 2 := by
      ring
    rw [hsq]
    have hnn : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 2 := by positivity
    nlinarith [hnn]

#print axioms concreteDirichletPWQOData

end

end RHFormalization
