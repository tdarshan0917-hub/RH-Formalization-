import RHFormalization.CurrentFrontierEndpoint
namespace RHFormalization
set_option pp.proofs.withType false
-- Force evaluation: what does F_stage reduce to definitionally?
example (α : DFiniteStage) (s : ℂ) :
    selectedFiniteOperatorLayer.toStagePackage.F_stage α s = 0 := by
  unfold selectedFiniteOperatorLayer
  simp only [DFiniteStagePackageFromOperatorLayer.toStagePackage]
  sorry
end RHFormalization
