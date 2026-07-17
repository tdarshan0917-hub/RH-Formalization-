import RHFormalization.SelectedDirectDRoute
import RHFormalization.DOverlapPointwiseFromCompactUniform

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/--
Selected direct D route from compact-uniform F/R convergence.

This removes the manual pointwise `hF` and `hR` inputs.  The only remaining
pointwise convergence input is the B-stage convergence to `Bcan`.
-/
def selectedOperatorResolventBridgeDirect_from_compactUniform_FR
    (B : DBcanLimitData selectedFiniteOperatorLayer.toStagePackage)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (stageSplit : DFiniteStageSplitAPI selectedFiniteOperatorLayer.toStagePackage)
    (hR_alpha : R.alpha = F.alpha)
    (hRHP :
      RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0 ⊆ Ω)
    (hB :
      ∀ s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0,
        Filter.Tendsto
          (fun n : ℕ => selectedFiniteOperatorLayer.toStagePackage.B_stage (F.alpha n) s)
          Filter.atTop
          (nhds (B.Bcan s))) :
    OperatorResolventBridge :=
  selectedOperatorResolventBridgeDirect_from_pointwise
    B F R stageSplit
    (F.pointwise_F_stage_tendsto_of_RHP_subset_Omega hRHP)
    hB
    (by
      intro s hs
      have h :=
        R.pointwise_R_stage_tendsto_of_RHP_subset_Omega hRHP s hs
      simpa [hR_alpha] using h)

#print axioms selectedOperatorResolventBridgeDirect_from_compactUniform_FR

end
end RHFormalization
