import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromFR
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthWindowAPI

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFR

Chosen-length Appendix-D constructor reduced to aligned F/R limit data plus
the inverse-speed hypothesis for the chosen sharp-cutoff window.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the chosen-length sharp-cutoff detailed D construction using the selected
chosen-length window data/API.

This removes `W` and `Wapi` from the remaining selected-D input list.
-/
def buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFR
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
    (hR_alpha : R.alpha = S.alpha)
    (h_inv_speed_tendsto_zero :
      ∀ (K : Set ℝ),
        IsCompact K →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                (1 : ℝ) / S.sharpSpeed.toCompactSpeedAPI.speed K n < ε) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthFR
    finiteOperatorLayer
    S
    (chosenLengthWindowData finiteOperatorLayer S)
    (chosenLengthWindowAPI_of_invSpeed
      finiteOperatorLayer
      S
      h_inv_speed_tendsto_zero)
    F
    R
    h_R_stage_bound
    hσ
    hF_alpha
    hR_alpha

end

end RHFormalization
