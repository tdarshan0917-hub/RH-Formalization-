import RHFormalization.SelectedOperatorResolventBridgeDirect
import RHFormalization.DOverlapFromStageSplitLimits

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/--
Direct selected D route.

This is the architectural bypass of the stale `selectedY` wrapper:
given selected B/F/R and pointwise convergence of F/B/R along the same
alpha sequence, build the actual `OperatorResolventBridge` consumed by E/F.
-/
def selectedOperatorResolventBridgeDirect_from_pointwise
    (B : DBcanLimitData selectedFiniteOperatorLayer.toStagePackage)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (stageSplit : DFiniteStageSplitAPI selectedFiniteOperatorLayer.toStagePackage)
    (hF :
      ∀ s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0,
        Filter.Tendsto
          (fun n : ℕ => selectedFiniteOperatorLayer.toStagePackage.F_stage (F.alpha n) s)
          Filter.atTop
          (nhds (F.FH s)))
    (hB :
      ∀ s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0,
        Filter.Tendsto
          (fun n : ℕ => selectedFiniteOperatorLayer.toStagePackage.B_stage (F.alpha n) s)
          Filter.atTop
          (nhds (B.Bcan s)))
    (hR :
      ∀ s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0,
        Filter.Tendsto
          (fun n : ℕ => selectedFiniteOperatorLayer.toStagePackage.R_stage (F.alpha n) s)
          Filter.atTop
          (nhds (R.RH s))) :
    OperatorResolventBridge :=
  selectedOperatorResolventBridgeDirect B F R
    (DOverlapIdentityAPI_from_pointwise_stage_limits
      stageSplit hF hB hR)

#print axioms selectedOperatorResolventBridgeDirect_from_pointwise

end
end RHFormalization
