import RHFormalization.SelectedFiniteTraceSpikePayload

/-!
# Selected finite operator layer

This file is conditional wiring only.

The actual selected finite trace/spike payload is still the open D-side target:

`selectedFiniteTraceSpikePayload : SelectedFiniteTraceSpikePayload`.

Once that instance exists, this file turns it into a
`DFiniteStagePackageFromOperatorLayer`.
-/

namespace RHFormalization

noncomputable section

def selectedFiniteOperatorLayer_from_traceSpikePayload
  (Pld : SelectedFiniteTraceSpikePayload) :
  DFiniteStagePackageFromOperatorLayer :=
buildSelectedFiniteOperatorLayerFromTraceSpikePayload Pld

end

end RHFormalization
