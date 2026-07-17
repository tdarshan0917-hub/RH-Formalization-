import RHFormalization.SelectedDirectDRouteFromFiniteCanonicalLimit
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/--
Final direct selected D bridge reducer.

This is the payoff of the pivot:
no selectedY wrapper,
no all-stage `h_R_stage_bound`,
no manual stageSplit,
no manual RHP⊂Ω.

Remaining selected-D burden:
`C`, `L`, `F`, `R`, alpha alignment, and sigma nonnegativity.
-/
def selectedOperatorResolventBridgeDirect_from_final_D_inputs
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer C)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (hR_alpha : R.alpha = F.alpha)
    (hF_alpha : F.alpha = L.alpha)
    (hσ : 0 ≤ selectedFiniteOperatorLayer.toStagePackage.sigma0) :
    OperatorResolventBridge :=
  selectedOperatorResolventBridgeDirect_from_finiteCanonicalLimit
    C L F R
    selectedFiniteOperatorLayer.toStageSplit
    hR_alpha
    hF_alpha
    (by
      exact rightHalfPlane_subset_Omega
        selectedFiniteOperatorLayer.toStagePackage.sigma0 hσ)

#print axioms selectedOperatorResolventBridgeDirect_from_final_D_inputs

end
end RHFormalization
