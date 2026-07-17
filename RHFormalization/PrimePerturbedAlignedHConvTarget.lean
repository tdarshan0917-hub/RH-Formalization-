import RHFormalization.PrimePerturbedDMasterResidualAligned
import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.PrimePerturbedDCANREMTarget
import RHFormalization.DCanRemFromMontel
import Mathlib

/-!
# h_conv target for aligned prime-perturbed layer

This file names the exact convergence input needed by
`primePerturbedDMasterResidualAligned_from_inputs`.

It separates:
* all-Ω local boundedness / D.CAN-REM target;
* overlap seed;
* Montel/Vitali convergence theorem.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- Exact h_conv shape required by the aligned DMasterResidual constructor. -/
def PrimePerturbedAlignedHConv
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (R_H : ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∀ ε : ℝ,
        0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ,
              s ∈ K →
                dist
                  ((primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                    (alpha n) s)
                  (R_H s) < ε

/-- Montel route to h_conv, once its standard inputs are supplied. -/
theorem primePerturbedAligned_hconv_from_montel
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (R_H : ℂ → ℂ)
    (h_stage_holo :
      ∀ n : ℕ,
        HolomorphicOnC
          (fun s =>
            (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
              (alpha n) s) Ω)
    (h_loc_bdd :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∃ C : ℝ,
            ∀ n : ℕ,
            ∀ s : ℂ,
              s ∈ K →
                ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                  (alpha n) s‖ ≤ C)
    (h_overlap :
      ∃ U : Set ℂ,
        IsOpen U ∧
        U.Nonempty ∧
        U ⊆ Ω ∧
          ∀ s ∈ U,
            Filter.Tendsto
              (fun n =>
                (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                  (alpha n) s)
              atTop
              (nhds (R_H s)))
    (hMontel :
      HolomorphicMontelConvergence
        (fun n s =>
          (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
            (alpha n) s)
        R_H) :
    PrimePerturbedAlignedHConv μ alpha R_H :=
  hMontel h_stage_holo h_loc_bdd h_overlap

#print axioms PrimePerturbedAlignedHConv
#print axioms primePerturbedAligned_hconv_from_montel

end
end RHFormalization
