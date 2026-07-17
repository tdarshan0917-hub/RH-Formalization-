import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.PrimePerturbedFStage
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.ArithmeticPrimeShiftedLaplaceBStage
import RHFormalization.ArithmeticShiftedLaplaceBStageFiniteCanonical
import RHFormalization.PrimePerturbedPayload
import Mathlib

/-!
# Prime-perturbed payload, B-ALIGNED to the banked closed-ball bound

Same operator F (primePerturbedFStage) but B = arithmeticShiftedLaplaceBStage —
the EXACT B the banked `ArithmeticPrimeDExport_on_closedBall_shiftedLaplaceBStage`
estimate is proven against. h_B_stage_eq_finiteCanonical IS the bridge theorem.
This aligns F, B, and residual to the banked bound by construction.
-/

namespace RHFormalization
open Complex Set

/-- B-aligned prime-perturbed payload: B = arithmeticShiftedLaplaceBStage. -/
noncomputable def primePerturbedPayloadAligned (μ : Fin N → ℝ) :
    SelectedFiniteCanonicalPayload :=
{ F_stage := fun α s =>
    primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s
  B_stage := fun α s => arithmeticShiftedLaplaceBStage α s
  R_stage := fun α s =>
    primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s -
      arithmeticShiftedLaplaceBStage α s
  sigma0 := 1
  h_stage_split := by intro α s hs; ring
  indices := fun α => α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP
  kernel := fun _ => shiftedLaplaceHeatKernelC
  h_B_stage_eq_finiteCanonical := by
    intro α s
    exact arithmeticShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image α s }

#print axioms primePerturbedPayloadAligned

end RHFormalization
