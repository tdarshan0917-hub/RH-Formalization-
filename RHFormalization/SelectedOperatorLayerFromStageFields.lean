import RHFormalization.SelectedTracePayloadFromStageFieldsClosed
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge

/-!
# RHFormalization.SelectedOperatorLayerFromStageFields

EF21.

Builds the finite operator layer from the closed stage-field trace/spike payload.

This continues the h_holo route:

DFiniteStage fields
→ selected trace/spike payload
→ selected finite operator layer

It does not touch endpoints.
It does not assume h_holo.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
The finite operator layer built from the closed stage-field trace/spike payload.
-/
def selectedFiniteOperatorLayer_fromStageFields :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromTraceSpikePayload
    selectedFiniteTraceSpikePayload_fromStageFields_closed

#print axioms selectedFiniteOperatorLayer_fromStageFields

end

end RHFormalization
