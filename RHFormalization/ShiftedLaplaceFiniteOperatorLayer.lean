import RHFormalization.DesignedOperatorLayer
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.PrimeSideTransformKernelPrototype

/-!
# Shifted-Laplace finite operator layer

A `DFiniteStagePackageFromOperatorLayer` whose finite-stage `B_stage` computes the
SHIFTED-LAPLACE kernel (not the displacement kernel). Reuses every kernel-agnostic
field of the designed spike witness (active indices, Nat→prime-power map, soundness,
completeness, injectivity, coefficient compatibility) and only changes the canonical
kernel to `shiftedLaplaceHeatKernelC`.
-/

namespace RHFormalization

noncomputable section

open RHFormalization

/-- The shifted-Laplace canonical kernel choice (stage-independent). -/
noncomputable def shiftedLaplaceKcan : DFiniteStage → CanonicalKernelC :=
  fun _ => shiftedLaplaceHeatKernelC

/-- Shifted-Laplace spike kernel induced via the designed witness's Nat→prime-power map. -/
noncomputable def shiftedLaplaceSpikeKernel : DFiniteStage → ℕ → ℂ → ℂ :=
  fun α n s =>
    shiftedLaplaceKcan α (PrimePowerPair.center (designedSpikeWitness.toPP α n)) s

/-- Shifted-Laplace finite diagonal-spike B_stage. -/
noncomputable def shiftedLaplaceB_stage : DFiniteStage → ℂ → ℂ :=
  fun α s =>
    finiteNatSpikePackage
      (designedSpikeWitness.activeIndices α)
      α.diagonalSpikeContribution
      (shiftedLaplaceSpikeKernel α)
      s

/-- Shifted-Laplace remainder. -/
noncomputable def shiftedLaplaceR_stage : DFiniteStage → ℂ → ℂ :=
  fun α s =>
    designedSpikeWitness.F_stage α s - shiftedLaplaceB_stage α s

theorem shiftedLaplace_stage_split :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane designedSpikeWitness.sigma0,
      designedSpikeWitness.F_stage α s = shiftedLaplaceB_stage α s + shiftedLaplaceR_stage α s := by
  intro α s hs
  simp [shiftedLaplaceR_stage]

theorem shiftedLaplace_B_stage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      shiftedLaplaceB_stage α s =
        finiteNatSpikePackage
          (designedSpikeWitness.activeIndices α)
          α.diagonalSpikeContribution
          (shiftedLaplaceSpikeKernel α)
          s := by
  intro α s; rfl

theorem shiftedLaplace_hkernel :
    ∀ (α : DFiniteStage), ∀ n ∈ designedSpikeWitness.activeIndices α, ∀ s : ℂ,
      shiftedLaplaceSpikeKernel α n s =
        shiftedLaplaceKcan α (designedSpikeWitness.toPP α n).center s := by
  intro α n hn s; rfl

/-- The shifted-Laplace selected finite trace/spike payload. -/
noncomputable def shiftedLaplaceTraceSpikePayload : SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    designedSpikeWitness.F_stage
    shiftedLaplaceB_stage
    shiftedLaplaceR_stage
    designedSpikeWitness.sigma0
    shiftedLaplace_stage_split
    designedSpikeWitness.activeIndices
    shiftedLaplaceSpikeKernel
    designedSpikeWitness.h_activeIndices_active
    shiftedLaplace_B_stage_eq_diagonal_sum
    designedSpikeWitness.toPP
    shiftedLaplaceKcan
    designedSpikeWitness.hinj
    designedSpikeWitness.hcoeff
    shiftedLaplace_hkernel

/-- **The shifted-Laplace finite operator layer.** Its `B_stage` computes the
shifted-Laplace kernel finite sum. -/
noncomputable def shiftedLaplaceFiniteOperatorLayer : DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromTraceSpikePayload shiftedLaplaceTraceSpikePayload

end

end RHFormalization
