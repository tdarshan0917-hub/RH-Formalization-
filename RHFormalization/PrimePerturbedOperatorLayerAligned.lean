import RHFormalization.PrimePerturbedPayloadAligned
import RHFormalization.PrimePerturbedDCANREMTarget
import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.DResidualBulkSectorHelpers
import Mathlib

/-!
# Aligned prime-perturbed operator layer

This is the operator layer built from the B-aligned payload:
F = primePerturbedFStage
B = arithmeticShiftedLaplaceBStage
R = F - B

This file wires the named D.CAN-REM target into the actual stage package
consumed downstream.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- The aligned prime-perturbed operator layer. -/
noncomputable def primePerturbedOperatorLayerAligned {N : ℕ} (μ : Fin N → ℝ) :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromCanonicalPayload
    (primePerturbedPayloadAligned μ)

/-- The named D.CAN-REM target gives the actual `R_stage` bound for the aligned layer. -/
theorem primePerturbedAligned_R_stage_bound_from_target
    {N : ℕ} (μ : Fin N → ℝ)
    (h : PrimePerturbedAlignedAllOmegaRStageBound μ) :
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∃ C : ℝ,
          0 ≤ C ∧
            ∀ α : DFiniteStage,
            ∀ s : ℂ,
              s ∈ K →
                ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C, hC0, hC⟩ := h K hK hKΩ
  refine ⟨C, hC0, ?_⟩
  intro α s hs
  simpa [primePerturbedOperatorLayerAligned, primePerturbedPayloadAligned] using hC α s hs

/-- Once D.CAN-REM is proved, the residual bulk-sector API follows immediately. -/
theorem primePerturbedAligned_bulkSectorBounds_from_target
    {N : ℕ} (μ : Fin N → ℝ)
    (h : PrimePerturbedAlignedAllOmegaRStageBound μ) :
    DResidualSectorBoundsAPI
      (primePerturbedOperatorLayerAligned μ).toStagePackage
      (residualBulkSectorData
        (primePerturbedOperatorLayerAligned μ).toStagePackage) :=
  residualBulkSectorBoundsAPI_of_R_stage_bound
    (primePerturbedOperatorLayerAligned μ).toStagePackage
    (primePerturbedAligned_R_stage_bound_from_target μ h)

#print axioms primePerturbedOperatorLayerAligned
#print axioms primePerturbedAligned_R_stage_bound_from_target
#print axioms primePerturbedAligned_bulkSectorBounds_from_target

end
end RHFormalization
