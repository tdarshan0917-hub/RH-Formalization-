import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.ResolventStageConvergence
import RHFormalization.ResolventLocalBound
import RHFormalization.DirichletPWQOToOperatorEigenvalue
import RHFormalization.EigenvalueGrowthSummable

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

private def cLam : ℕ → ℝ := fun n => ((n : ℝ) * Real.pi) ^ 2

theorem concrete_summable_resolvent :
    Summable (fun n => (1 + cLam n)⁻¹) :=
  summable_resolvent_of_weyl cLam
    (fun n => by unfold cLam; positivity)
    concreteDirichletPWQOData.growthConst 0
    concreteDirichletPWQOData.growthConst_pos
    (by
      intro n
      have h := concreteDirichletPWQOData.growth_sq n
      have : concreteDirichletPWQOData.growthConst * (n : ℝ) ^ 2 - 0 ≤ cLam n := by
        simpa [cLam, concreteDirichletPWQOData] using h
      exact this)

#print axioms concrete_summable_resolvent
end
end RHFormalization
