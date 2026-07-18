import RHFormalization.DOperatorExport
import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-
Purpose:
Check whether the selected finite providers can be taken directly from
DFiniteStage fields, instead of remaining as `?F_stage`, `?indices`,
`?activeIndices`, and `?toPP`.

This is the h_holo model-alignment gate. It does not touch endpoints.
-/

#check DFiniteStage
#check DFiniteStage.appendixDFiniteFStage
#check DFiniteStage.diagonalSpikeActiveIndices
#check DFiniteStage.diagonalSpikeToPP
#check DFiniteStage.diagonalSpikeContribution

#check AppendixDFiniteSpikeExtractionWitness
#check selectedAppendixDFiniteSpikeExtractionWitness

/-- Candidate real finite-stage transform provider. -/
noncomputable def selectedFiniteFStage_fromStage :
    DFiniteStage → ℂ → ℂ :=
  fun α => α.appendixDFiniteFStage

/-- Candidate active Nat-index provider. -/
noncomputable def selectedTraceActiveIndices_fromStage :
    DFiniteStage → Finset ℕ :=
  fun α => α.diagonalSpikeActiveIndices

/-- Candidate Nat-to-prime-power provider. -/
noncomputable def selectedTraceToPP_fromStage :
    DFiniteStage → ℕ → PrimePowerPair :=
  fun α => α.diagonalSpikeToPP

#print axioms selectedFiniteFStage_fromStage
#print axioms selectedTraceActiveIndices_fromStage
#print axioms selectedTraceToPP_fromStage

end

end RHFormalization
