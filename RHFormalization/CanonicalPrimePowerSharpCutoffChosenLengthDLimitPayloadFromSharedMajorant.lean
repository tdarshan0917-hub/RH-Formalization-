import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayload
import RHFormalization.CanonicalPrimePowerSharpCutoffSharedLimitMajorant

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromSharedMajorant

Lift the final chosen-length D payload boundary one step upstream:
from a chosen-length mass-envelope package to a chosen-length shared-majorant
package.

The shared-majorant package supplies the `S` field of `ChosenLengthDLimitPayload`
via `toChosenLengthMassEnvelopeData`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the final chosen-length D payload from a chosen-length shared-majorant
package plus the remaining FH/RH analytic limit payload.
-/
def buildChosenLengthDLimitPayloadFromSharedMajorant
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S0 :
      CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData
        finiteOperatorLayer)
    (FH RH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.F_stage
                      (S0.toChosenLengthMassEnvelopeData.alpha n) s)
                    (FH s) < ε)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.R_stage
                      (S0.toChosenLengthMassEnvelopeData.alpha n) s)
                    (RH s) < ε)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∃ C, 0 ≤ C ∧
            ∀ (α : DFiniteStage), ∀ s ∈ K,
              ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0) :
    ChosenLengthDLimitPayload :=
  { finiteOperatorLayer := finiteOperatorLayer
    S := S0.toChosenLengthMassEnvelopeData
    FH := FH
    RH := RH
    h_FH_holo := h_FH_holo
    h_RH_holo := h_RH_holo
    h_F_stage_to_FH := h_F_stage_to_FH
    h_R_stage_to_RH := h_R_stage_to_RH
    h_R_stage_bound := h_R_stage_bound
    hσ := hσ }

/--
Directly build the D-side final input from a chosen-length shared-majorant
package plus the remaining FH/RH analytic limit payload.
-/
def buildDDetailedConstructionWithOperatorLegalityFromChosenLengthSharedMajorantPayload
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S0 :
      CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData
        finiteOperatorLayer)
    (FH RH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.F_stage
                      (S0.toChosenLengthMassEnvelopeData.alpha n) s)
                    (FH s) < ε)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.R_stage
                      (S0.toChosenLengthMassEnvelopeData.alpha n) s)
                    (RH s) < ε)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∃ C, 0 ≤ C ∧
            ∀ (α : DFiniteStage), ∀ s ∈ K,
              ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromChosenLengthDLimitPayload
    (buildChosenLengthDLimitPayloadFromSharedMajorant
      finiteOperatorLayer
      S0
      FH
      RH
      h_FH_holo
      h_RH_holo
      h_F_stage_to_FH
      h_R_stage_to_RH
      h_R_stage_bound
      hσ)

end

end RHFormalization
