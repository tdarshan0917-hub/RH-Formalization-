import RHFormalization.SelectedDirectDRouteFromCompactUniformFR
import RHFormalization.AppendixDPrimePowerLimitReduction

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/--
Selected direct D route using the existing finite-canonical B-limit provider.

This uses the repo's established route:
`DOperatorFiniteCanonicalLimitAtOverlapData`
→ `buildDBcanLimitDataFromOperatorFiniteCanonicalLimit`
→ B-stage convergence.
-/
def selectedOperatorResolventBridgeDirect_from_finiteCanonicalLimit
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer C)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (stageSplit : DFiniteStageSplitAPI selectedFiniteOperatorLayer.toStagePackage)
    (hR_alpha : R.alpha = F.alpha)
    (hF_alpha : F.alpha = L.alpha)
    (hRHP :
      RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0 ⊆ Ω) :
    OperatorResolventBridge :=
  let B : DBcanLimitData selectedFiniteOperatorLayer.toStagePackage :=
    buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
      selectedFiniteOperatorLayer C L
  selectedOperatorResolventBridgeDirect_from_compactUniform_FR
    B F R stageSplit hR_alpha hRHP
    (by
      intro s hs
      have h :=
        (buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit
          selectedFiniteOperatorLayer C L).h_B_stage_tendsto_Bcan s hs
      simpa [hF_alpha] using h)

#print axioms selectedOperatorResolventBridgeDirect_from_finiteCanonicalLimit

end
end RHFormalization
