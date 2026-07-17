import RHFormalization.SelectedTracePayloadFromStageFields

/-!
# RHFormalization.SelectedTracePayloadFromStageFieldsClosed

EF19.

Closes the stage-field selected trace/spike payload constructor using the proof
fields already stored inside `DFiniteStage`.

EF18 showed the required facts are not missing:

* `h_diagonalSpikeActiveIndices_active`
* `h_diagonalSpikeToPP_inj`
* `h_canonicalSpikeContribution_eq_weightC`

This file turns the EF17 conditional constructor into an unconditional payload.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
The selected finite trace/spike payload built directly from the real
`DFiniteStage` fields.
-/
def selectedFiniteTraceSpikePayload_fromStageFields_closed :
    SelectedFiniteTraceSpikePayload :=
  selectedFiniteTraceSpikePayload_fromStageFields
    (fun α q hq =>
      α.h_diagonalSpikeActiveIndices_active q hq)
    (fun α m hm n hn hmn =>
      α.h_diagonalSpikeToPP_inj m hm n hn hmn)
    (fun α n hn =>
      α.h_canonicalSpikeContribution_eq_weightC n hn)

#print axioms selectedFiniteTraceSpikePayload_fromStageFields_closed

end

end RHFormalization
