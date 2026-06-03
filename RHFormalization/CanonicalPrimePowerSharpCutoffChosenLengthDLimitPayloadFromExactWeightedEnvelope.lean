import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromDisplacementKernel
import RHFormalization.CanonicalPrimePowerSharpCutoffExactWeightedEnvelope

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromExactWeightedEnvelope

Lift the selected chosen-length D payload boundary one more step upstream:
from a chosen-length displacement-kernel package to an exact-weighted-envelope
package.

The exact-weighted-envelope package supplies the displacement-kernel package
through `toDisplacementKernelData`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the final chosen-length D payload from an exact-weighted-envelope package
plus the remaining FH/RH analytic limit payload.
-/
def buildChosenLengthDLimitPayloadFromExactWeightedEnvelope
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (E0 :
      CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData
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
                      (E0.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
                      (E0.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
  buildChosenLengthDLimitPayloadFromDisplacementKernel
    finiteOperatorLayer
    E0.toDisplacementKernelData
    FH
    RH
    h_FH_holo
    h_RH_holo
    h_F_stage_to_FH
    h_R_stage_to_RH
    h_R_stage_bound
    hσ

/--
Directly build the D-side final input from an exact-weighted-envelope package
plus the remaining FH/RH analytic limit payload.
-/
def buildDDetailedConstructionWithOperatorLegalityFromExactWeightedEnvelopePayload
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (E0 :
      CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData
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
                      (E0.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
                      (E0.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
    (buildChosenLengthDLimitPayloadFromExactWeightedEnvelope
      finiteOperatorLayer
      E0
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
