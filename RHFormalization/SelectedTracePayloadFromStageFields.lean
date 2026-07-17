import RHFormalization.DFiniteStageProviderFields
import RHFormalization.SelectedFiniteTraceSpikePayload
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerDWindowKernelIdentification

/-!
# RHFormalization.SelectedTracePayloadFromStageFields

EF17.

This file converts the EF16 scratch gate into a reusable selected trace/spike
payload constructor.

It uses the real `DFiniteStage` fields banked in EF14:

* `appendixDFiniteFStage`
* `diagonalSpikeActiveIndices`
* `diagonalSpikeToPP`
* `diagonalSpikeContribution`

The only remaining non-algebraic obligations are:

1. active-index activity;
2. injectivity of `diagonalSpikeToPP` on active indices;
3. coefficient compatibility.

This does not prove RH and does not touch endpoints.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- Selected half-plane threshold for the stage-field trace payload. -/
noncomputable def stageFieldTraceSigma0 : ℝ := 0

/-- Current canonical kernel used by the selected finite trace package. -/
noncomputable def stageFieldTraceKcan :
    DFiniteStage → CanonicalKernelC :=
  fun _ => displacementCanonicalKernel (heatKernelG (1 : ℝ))

/-- Nat-indexed spike kernel from the real `diagonalSpikeToPP` field. -/
noncomputable def stageFieldTraceSpikeKernel :
    DFiniteStage → ℕ → ℂ → ℂ :=
  fun α n s =>
    stageFieldTraceKcan α
      (PrimePowerPair.center (selectedTraceToPP_fromStage α n))
      s

/-- Finite canonical part from real active indices and real contribution field. -/
noncomputable def stageFieldTraceBStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    finiteNatSpikePackage
      (selectedTraceActiveIndices_fromStage α)
      (selectedTraceContribution_fromStage α)
      (stageFieldTraceSpikeKernel α)
      s

/-- Remainder defined algebraically from the real finite-stage transform. -/
noncomputable def stageFieldTraceRStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    selectedFiniteFStage_fromStage α s - stageFieldTraceBStage α s

/-- Algebraic stage split. -/
theorem stageFieldTraceStageSplit :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane stageFieldTraceSigma0,
      selectedFiniteFStage_fromStage α s =
        stageFieldTraceBStage α s + stageFieldTraceRStage α s := by
  intro α s hs
  simp [stageFieldTraceRStage]

/-- Definitional diagonal-sum identity. -/
theorem stageFieldTraceBStage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      stageFieldTraceBStage α s =
        finiteNatSpikePackage
          (selectedTraceActiveIndices_fromStage α)
          α.diagonalSpikeContribution
          (stageFieldTraceSpikeKernel α)
          s := by
  intro α s
  rfl

/-- Definitional kernel bridge. -/
theorem stageFieldTraceKernelBridge :
    ∀ (α : DFiniteStage), ∀ n ∈ selectedTraceActiveIndices_fromStage α, ∀ (s : ℂ),
      stageFieldTraceSpikeKernel α n s =
        stageFieldTraceKcan α
          (PrimePowerPair.center (selectedTraceToPP_fromStage α n))
          s := by
  intro α n hn s
  rfl

/--
Build the selected finite trace/spike payload from the real `DFiniteStage`
fields, reducing the construction to exactly three remaining provider facts.
-/
def selectedFiniteTraceSpikePayload_fromStageFields
    (h_activeIndices_active :
      ∀ (α : DFiniteStage), ∀ q ∈ selectedTraceActiveIndices_fromStage α,
        α.diagonalSpikeActive q)
    (hinj :
      ∀ (α : DFiniteStage),
        ∀ m ∈ selectedTraceActiveIndices_fromStage α,
        ∀ n ∈ selectedTraceActiveIndices_fromStage α,
          selectedTraceToPP_fromStage α m =
            selectedTraceToPP_fromStage α n → m = n)
    (hcoeff :
      ∀ (α : DFiniteStage), ∀ n ∈ selectedTraceActiveIndices_fromStage α,
        α.canonicalSpikeContribution n =
          (selectedTraceToPP_fromStage α n).weightC) :
    SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    selectedFiniteFStage_fromStage
    stageFieldTraceBStage
    stageFieldTraceRStage
    stageFieldTraceSigma0
    stageFieldTraceStageSplit
    selectedTraceActiveIndices_fromStage
    stageFieldTraceSpikeKernel
    h_activeIndices_active
    stageFieldTraceBStage_eq_diagonal_sum
    selectedTraceToPP_fromStage
    stageFieldTraceKcan
    hinj
    hcoeff
    stageFieldTraceKernelBridge

#print axioms stageFieldTraceSigma0
#print axioms stageFieldTraceKcan
#print axioms stageFieldTraceSpikeKernel
#print axioms stageFieldTraceBStage
#print axioms stageFieldTraceRStage
#print axioms stageFieldTraceStageSplit
#print axioms stageFieldTraceBStage_eq_diagonal_sum
#print axioms stageFieldTraceKernelBridge
#print axioms selectedFiniteTraceSpikePayload_fromStageFields

end

end RHFormalization
