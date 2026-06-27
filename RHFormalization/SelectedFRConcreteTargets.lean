import RHFormalization.SelectedFiniteCanonicalLimitConcrete
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualAlong
import RHFormalization.ArithmeticPrimeStageHolo
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Concrete selected F/R target layer.

C and L are now concrete:
  selectedDirectC
  selectedFiniteCanonicalLimitConcrete

The next selected-direct D inputs are:
  F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage
  R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage

This file fixes the shared alpha to match L:
  alpha n = primePowerStage n
-/

noncomputable def selectedDAlpha : ℕ → DFiniteStage :=
  fun n => primePowerStage n

theorem selectedL_alpha_eq_selectedDAlpha :
    selectedFiniteCanonicalLimitConcrete.alpha = selectedDAlpha := by
  rfl

/-- Exact F constructor target. -/
noncomputable def buildSelectedDFHLimit
    (FH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_F_stage_to_FH :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ s ∈ K,
              dist
                (selectedFiniteOperatorLayer.toStagePackage.F_stage
                  (selectedDAlpha n) s)
                (FH s) < ε) :
    DFHLimitData selectedFiniteOperatorLayer.toStagePackage :=
  buildDFHLimitDataFromCompactUniform
    selectedFiniteOperatorLayer.toStagePackage
    selectedDAlpha
    FH
    h_FH_holo
    h_F_stage_to_FH

/-- Exact R constructor target. -/
noncomputable def buildSelectedDMasterResidual
    (RH : ℂ → ℂ)
    (h_stage_holo :
      ∀ n : ℕ,
        HolomorphicOnC
          (fun s =>
            selectedFiniteOperatorLayer.toStagePackage.R_stage
              (selectedDAlpha n) s)
          Ω)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ s ∈ K,
              dist
                (selectedFiniteOperatorLayer.toStagePackage.R_stage
                  (selectedDAlpha n) s)
                (RH s) < ε) :
    DMasterResidualData selectedFiniteOperatorLayer.toStagePackage :=
  buildDMasterResidualDataAlong
    selectedFiniteOperatorLayer.toStagePackage
    selectedDAlpha
    RH
    h_stage_holo
    h_R_stage_to_RH

#print axioms buildSelectedDFHLimit
#print axioms buildSelectedDMasterResidual
#print axioms selectedL_alpha_eq_selectedDAlpha

end
end RHFormalization
