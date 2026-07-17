import RHFormalization.DOperatorExport
import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance

/-!
# RHFormalization.DFiniteStageProviderFields

EF14 provider-alignment layer for the h_holo / explicit-formula track.

This file banks the real fields already present on `DFiniteStage`:

* `appendixDFiniteFStage`
* `diagonalSpikeActiveIndices`
* `diagonalSpikeToPP`
* `diagonalSpikeContribution`

This is meant to replace/bypass placeholder selected-provider holes such as
`?F_stage`, `?indices`, `?activeIndices`, and `?toPP`.

It does not prove RH.
It does not touch `CurrentFrontierEndpoint`.
It does not touch hsum.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- The actual finite-stage operator transform stored on `DFiniteStage`. -/
noncomputable def selectedFiniteFStage_fromStage :
    DFiniteStage → ℂ → ℂ :=
  fun α => α.appendixDFiniteFStage

/-- The actual active diagonal-spike Nat indices stored on `DFiniteStage`. -/
noncomputable def selectedTraceActiveIndices_fromStage :
    DFiniteStage → Finset ℕ :=
  fun α => α.diagonalSpikeActiveIndices

/-- The actual Nat-to-prime-power map stored on `DFiniteStage`. -/
noncomputable def selectedTraceToPP_fromStage :
    DFiniteStage → ℕ → PrimePowerPair :=
  fun α => α.diagonalSpikeToPP

/-- The actual diagonal spike contribution stored on `DFiniteStage`. -/
noncomputable def selectedTraceContribution_fromStage :
    DFiniteStage → ℕ → ℂ :=
  fun α => α.diagonalSpikeContribution

@[simp] theorem selectedFiniteFStage_fromStage_apply
    (α : DFiniteStage) (s : ℂ) :
    selectedFiniteFStage_fromStage α s =
      α.appendixDFiniteFStage s := rfl

@[simp] theorem selectedTraceActiveIndices_fromStage_apply
    (α : DFiniteStage) :
    selectedTraceActiveIndices_fromStage α =
      α.diagonalSpikeActiveIndices := rfl

@[simp] theorem selectedTraceToPP_fromStage_apply
    (α : DFiniteStage) (n : ℕ) :
    selectedTraceToPP_fromStage α n =
      α.diagonalSpikeToPP n := rfl

@[simp] theorem selectedTraceContribution_fromStage_apply
    (α : DFiniteStage) (n : ℕ) :
    selectedTraceContribution_fromStage α n =
      α.diagonalSpikeContribution n := rfl

#print axioms selectedFiniteFStage_fromStage
#print axioms selectedTraceActiveIndices_fromStage
#print axioms selectedTraceToPP_fromStage
#print axioms selectedTraceContribution_fromStage

#print axioms selectedFiniteFStage_fromStage_apply
#print axioms selectedTraceActiveIndices_fromStage_apply
#print axioms selectedTraceToPP_fromStage_apply
#print axioms selectedTraceContribution_fromStage_apply

end

end RHFormalization
