import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromLimits
import RHFormalization.RealLayerDMasterProbe
import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.DFHLimitConcrete
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/-- realY on the REAL prime layer: builder applied to primePerturbedOperatorLayerAligned,
with R from realLayerDMaster's DMasterResidualData. Remaining inputs named explicitly. -/
def realPrimeY
    (μ : Fin N → ℝ)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
          (primePerturbedOperatorLayerAligned μ))
    (FH RH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FH :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∀ (ε : ℝ), 0 < ε →
          ∀ᶠ (n : ℕ) in Filter.atTop, ∀ s ∈ K,
            dist ((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (S.alpha n) s) (FH s) < ε)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∀ (ε : ℝ), 0 < ε →
          ∀ᶠ (n : ℕ) in Filter.atTop, ∀ s ∈ K,
            dist ((primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (S.alpha n) s) (RH s) < ε)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ (primePerturbedOperatorLayerAligned μ).toStagePackage.sigma0) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthLimits
    (primePerturbedOperatorLayerAligned μ)
    S
    FH RH
    h_FH_holo h_RH_holo
    h_F_stage_to_FH h_R_stage_to_RH
    h_R_stage_bound
    hσ

#print axioms realPrimeY

end
end RHFormalization
