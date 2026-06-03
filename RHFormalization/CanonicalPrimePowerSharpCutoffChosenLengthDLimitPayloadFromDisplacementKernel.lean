import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromSharedMajorant
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromDisplacementKernel

Lift the selected chosen-length D payload boundary one more step upstream:
from a chosen-length shared-majorant package to a chosen-length displacement-kernel
package.

The displacement-kernel package supplies the shared-majorant package through
`toSharedMajorantData`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the final chosen-length D payload from a chosen-length displacement-kernel
package plus the remaining FH/RH analytic limit payload.
-/
def buildChosenLengthDLimitPayloadFromDisplacementKernel
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (D0 :
      CanonicalPrimePowerSharpCutoffChosenLengthDisplacementKernelData
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
                      (D0.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
                      (D0.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
  buildChosenLengthDLimitPayloadFromSharedMajorant
    finiteOperatorLayer
    D0.toSharedMajorantData
    FH
    RH
    h_FH_holo
    h_RH_holo
    h_F_stage_to_FH
    h_R_stage_to_RH
    h_R_stage_bound
    hσ

/--
Directly build the D-side final input from a chosen-length displacement-kernel
package plus the remaining FH/RH analytic limit payload.
-/
def buildDDetailedConstructionWithOperatorLegalityFromChosenLengthDisplacementKernelPayload
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (D0 :
      CanonicalPrimePowerSharpCutoffChosenLengthDisplacementKernelData
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
                      (D0.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
                      (D0.toSharedMajorantData.toChosenLengthMassEnvelopeData.alpha n) s)
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
    (buildChosenLengthDLimitPayloadFromDisplacementKernel
      finiteOperatorLayer
      D0
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
