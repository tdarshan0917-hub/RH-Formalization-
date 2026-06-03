import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFR
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthInvSpeed

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed

Chosen-length Appendix-D constructor with the inverse-speed hypothesis discharged.

After this file, the remaining selected-D inputs are only:
`F`, `R`, residual stage bound, sigma nonnegativity, and alpha alignment.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the chosen-length sharp-cutoff detailed D construction using the selected
window package, with inverse-speed already supplied by
`chosenLength_inv_speed_tendsto_zero`.
-/
def buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (R : DMasterResidualData finiteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
            ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFR
    finiteOperatorLayer
    S
    F
    R
    h_R_stage_bound
    hσ
    hF_alpha
    hR_alpha
    (chosenLength_inv_speed_tendsto_zero finiteOperatorLayer S)

end

end RHFormalization
