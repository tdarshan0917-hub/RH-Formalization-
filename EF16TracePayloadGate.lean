import RHFormalization.DFiniteStageProviderFields
import RHFormalization.SelectedFiniteTraceSpikePayload
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerDWindowKernelIdentification

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-
EF16 purpose:

We are not proving the displacement-kernel principal part.
That is the loop.

We are checking whether the selected finite trace/spike payload can now be built
from the real DFiniteStage fields banked in EF14:

  F_stage        := α.appendixDFiniteFStage
  activeIndices := α.diagonalSpikeActiveIndices
  toPP          := α.diagonalSpikeToPP
  contribution  := α.diagonalSpikeContribution

The goal is to isolate the remaining real provider obligations:
  1. active-index activity
  2. injectivity of diagonalSpikeToPP on active indices
  3. coefficient compatibility
-/

#check SelectedFiniteTraceSpikePayload
#check buildSelectedFiniteTraceSpikePayloadFromImageBridge

#check selectedFiniteFStage_fromStage
#check selectedTraceActiveIndices_fromStage
#check selectedTraceToPP_fromStage
#check selectedTraceContribution_fromStage

#check DFiniteStage.appendixDFiniteFStage
#check DFiniteStage.diagonalSpikeActiveIndices
#check DFiniteStage.diagonalSpikeToPP
#check DFiniteStage.diagonalSpikeContribution

/-- Selected half-plane threshold for this provider gate. -/
noncomputable def ef16TraceSigma0 : ℝ := 0

/-- Still the current canonical kernel; this is exactly what we are testing. -/
noncomputable def ef16TraceKcan :
    DFiniteStage → CanonicalKernelC :=
  fun _ => displacementCanonicalKernel (heatKernelG (1 : ℝ))

/-- Nat-indexed spike kernel from the real `diagonalSpikeToPP` field. -/
noncomputable def ef16TraceSpikeKernel :
    DFiniteStage → ℕ → ℂ → ℂ :=
  fun α n s =>
    ef16TraceKcan α
      (PrimePowerPair.center (selectedTraceToPP_fromStage α n))
      s

/-- Finite canonical part from the real active indices and real contribution field. -/
noncomputable def ef16TraceBStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    finiteNatSpikePackage
      (selectedTraceActiveIndices_fromStage α)
      (selectedTraceContribution_fromStage α)
      (ef16TraceSpikeKernel α)
      s

/-- Remainder defined algebraically from the real finite-stage operator transform. -/
noncomputable def ef16TraceRStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    selectedFiniteFStage_fromStage α s - ef16TraceBStage α s

/-- Algebraic split: this should be definitional. -/
theorem ef16TraceStageSplit :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane ef16TraceSigma0,
      selectedFiniteFStage_fromStage α s =
        ef16TraceBStage α s + ef16TraceRStage α s := by
  intro α s hs
  simp [ef16TraceRStage]

/-- Definitional diagonal-sum identity. -/
theorem ef16TraceBStage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      ef16TraceBStage α s =
        finiteNatSpikePackage
          (selectedTraceActiveIndices_fromStage α)
          (selectedTraceContribution_fromStage α)
          (ef16TraceSpikeKernel α)
          s := by
  intro α s
  rfl

/-- Definitional kernel bridge. -/
theorem ef16TraceKernelBridge :
    ∀ (α : DFiniteStage), ∀ n ∈ selectedTraceActiveIndices_fromStage α, ∀ (s : ℂ),
      ef16TraceSpikeKernel α n s =
        ef16TraceKcan α
          (PrimePowerPair.center (selectedTraceToPP_fromStage α n))
          s := by
  intro α n hn s
  rfl

#print axioms ef16TraceSigma0
#print axioms ef16TraceKcan
#print axioms ef16TraceSpikeKernel
#print axioms ef16TraceBStage
#print axioms ef16TraceRStage
#print axioms ef16TraceStageSplit
#print axioms ef16TraceBStage_eq_diagonal_sum
#print axioms ef16TraceKernelBridge

end

end RHFormalization
