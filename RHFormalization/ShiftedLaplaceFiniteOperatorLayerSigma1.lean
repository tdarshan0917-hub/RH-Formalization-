import RHFormalization.ShiftedLaplaceFiniteOperatorLayer

/-!
# Shifted-Laplace finite operator layer at σ = 1

Identical to `shiftedLaplaceFiniteOperatorLayer` but with the half-plane
threshold `sigma0 := 1` instead of the displacement witness's `0`. The threshold
only appears in the `stage_split` obligation (`F = B + R` on `RightHalfPlane sigma0`),
which holds for ANY sigma0 since `R := F - B` (definitional).

This is the threshold that matches the shifted-Laplace kernel's convergence:
`RightHalfPlane 1 ⊆ shiftedLaplaceAbsConvRegion` (proved in
`ShiftedLaplaceSqrtReLowerBound`).
-/

namespace RHFormalization

noncomputable section

open RHFormalization

/-- Stage split at threshold 1 (definitional, since `R := F - B`). -/
theorem shiftedLaplace_stage_split_sigma1 :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane (1 : ℝ),
      designedSpikeWitness.F_stage α s
        = shiftedLaplaceB_stage α s + shiftedLaplaceR_stage α s := by
  intro α s _
  simp [shiftedLaplaceR_stage]

/-- The shifted-Laplace selected finite trace/spike payload at σ = 1. -/
noncomputable def shiftedLaplaceTraceSpikePayloadSigma1 : SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    designedSpikeWitness.F_stage
    shiftedLaplaceB_stage
    shiftedLaplaceR_stage
    (1 : ℝ)
    shiftedLaplace_stage_split_sigma1
    designedSpikeWitness.activeIndices
    shiftedLaplaceSpikeKernel
    designedSpikeWitness.h_activeIndices_active
    shiftedLaplace_B_stage_eq_diagonal_sum
    designedSpikeWitness.toPP
    shiftedLaplaceKcan
    designedSpikeWitness.hinj
    designedSpikeWitness.hcoeff
    shiftedLaplace_hkernel

/-- **The shifted-Laplace finite operator layer at σ = 1.** -/
noncomputable def shiftedLaplaceFiniteOperatorLayerSigma1 : DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromTraceSpikePayload shiftedLaplaceTraceSpikePayloadSigma1

#print axioms shiftedLaplaceFiniteOperatorLayerSigma1

end

end RHFormalization
