import RHFormalization.SelectedFiniteCanonicalPayload

/-!
# Selected finite operator layer

Corrected conditional wiring.

The previous `SelectedFiniteTraceSpikePayload` route was too weak and allowed
empty/zero fake payloads.  The selected finite operator layer should instead be
built from the direct canonical finite prime-power payload:

`SelectedFiniteCanonicalPayload`.

The real remaining D-side proof target is now:

`selectedFiniteCanonicalPayload : SelectedFiniteCanonicalPayload`.
-/

namespace RHFormalization

noncomputable section

def selectedFiniteOperatorLayer_from_canonicalPayload
    (Pld : SelectedFiniteCanonicalPayload) :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromCanonicalPayload Pld

end

end RHFormalization
