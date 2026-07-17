import RHFormalization.CanonicalPrimePowerSharpCutoffClosedDWindowSource

/-!
# Selected closed heat-kernel weighted payload

The finite operator layer is built.  This file reduces the closed payload to
the single coherent sharp-cutoff D-window source theorem.
-/

namespace RHFormalization

noncomputable section

def selectedSharpCutoffClosedDWindowSource :
    SelectedSharpCutoffClosedDWindowSource :=
by
  exact ?selectedSharpCutoffClosedDWindowSource

def selectedClosedPayload :
    CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload :=
  buildSelectedClosedPayloadFromSharpCutoffSource
    selectedSharpCutoffClosedDWindowSource

def selectedH0 :
    CanonicalPrimePowerSharpCutoffHeatKernelWeightedData
      selectedClosedPayload.X :=
  buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataFromClosedPayload
    selectedClosedPayload

end

end RHFormalization
