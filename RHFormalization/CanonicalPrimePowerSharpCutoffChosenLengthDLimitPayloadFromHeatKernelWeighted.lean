import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromExactWeightedEnvelope
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromHeatKernelWeighted

Lift the selected chosen-length D payload boundary upstream from exact-weighted
envelope data to the heat-kernel weighted sharp-cutoff package.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the final chosen-length D payload from heat-kernel weighted sharp-cutoff
data plus the remaining FH/RH analytic limit payload.
-/
def buildChosenLengthDLimitPayloadFromHeatKernelWeighted
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (H0 :
      CanonicalPrimePowerSharpCutoffHeatKernelWeightedData
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
                      (H0.toExactWeightedEnvelopeData.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
                      (H0.toExactWeightedEnvelopeData.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
  buildChosenLengthDLimitPayloadFromExactWeightedEnvelope
    finiteOperatorLayer
    H0.toExactWeightedEnvelopeData
    FH
    RH
    h_FH_holo
    h_RH_holo
    h_F_stage_to_FH
    h_R_stage_to_RH
    h_R_stage_bound
    hσ

/--
Directly build the D-side final input from heat-kernel weighted sharp-cutoff data
plus the remaining FH/RH analytic limit payload.
-/
def buildDDetailedConstructionWithOperatorLegalityFromHeatKernelWeightedPayload
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (H0 :
      CanonicalPrimePowerSharpCutoffHeatKernelWeightedData
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
                      (H0.toExactWeightedEnvelopeData.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
                      (H0.toExactWeightedEnvelopeData.toDisplacementKernelData.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
    (buildChosenLengthDLimitPayloadFromHeatKernelWeighted
      finiteOperatorLayer
      H0
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
