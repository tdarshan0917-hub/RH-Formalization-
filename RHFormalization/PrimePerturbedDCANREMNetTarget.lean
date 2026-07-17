import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.PrimePerturbedDMasterResidualAligned
import RHFormalization.PrimePerturbedAlignedHConvTarget
import RHFormalization.RStageBoundAttack
import RHFormalization.DispMajorantSuperpoly
import RHFormalization.DispTransformBounded
import RHFormalization.AnchorFinite
import Mathlib

/-!
# Actual D.CAN-REM target along the real stage net

This avoids the over-strong fake-stage target

  ∀ α : DFiniteStage, ...

and states the theorem in the exact form consumed by
`buildDMasterResidualDataAlong` / `dcanrem_from_montel`:

  ∀ n : ℕ, along the actual admissible stage net.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- Exact local-boundedness target along the actual stage net. -/
def PrimePerturbedAlignedAlongRStageBound
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage) : Prop :=
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ n : ℕ,
          ∀ s : ℂ,
            s ∈ K →
              ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                  (alpha n) s‖ ≤ C

/-- Along-net bound gives the `h_loc_bdd` input required by Montel. -/
theorem primePerturbedAligned_h_loc_bdd_from_along_bound
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (h : PrimePerturbedAlignedAlongRStageBound μ alpha) :
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∃ C : ℝ,
          ∀ n : ℕ,
          ∀ s : ℂ,
            s ∈ K →
              ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                  (alpha n) s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C, _hC0, hC⟩ := h K hK hKΩ
  exact ⟨C, hC⟩

#check primePerturbedAligned_hconv_from_montel
#check primePerturbedDMasterResidualAligned_from_inputs
#check disp_majorant_superpoly
#check disp_transform_bounded
#check anchor_integrand_integrable
#check anchor_admissible

#print axioms PrimePerturbedAlignedAlongRStageBound
#print axioms primePerturbedAligned_h_loc_bdd_from_along_bound

end
end RHFormalization
