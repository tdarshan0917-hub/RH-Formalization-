import RHFormalization.SelectedRCutoffDetailedConstructionSource
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel

namespace RHFormalization

noncomputable section

def selectedRCutoffDetailedConstructionSource :
    SelectedRCutoffDetailedConstructionSource :=
by
  let W0 : DCanonicalWindowData :=
    sharpCutoffDCanonicalWindowData
      (heatKernelG (1 : ℝ))
      (fun α : DFiniteStage => α.L)

  refine
  {
    S := ?S
    W := W0
    Wapi := ?Wapi
    F := ?F
    sectors := ?sectors
    sectorSplit := ?sectorSplit
    sectorBounds := ?sectorBounds
    master := ?master
    overlapBuilder := ?overlapBuilder
  }

def selectedDDetailedConstructionWithOperatorLegality :
    DDetailedConstructionWithOperatorLegality :=
  buildSelectedDDetailedConstructionFromRCutoffSource
    selectedRCutoffDetailedConstructionSource

end

end RHFormalization
