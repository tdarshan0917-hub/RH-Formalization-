import RHFormalization.AppendixDRCutoffEstimateDetailedConstruction
import RHFormalization.SelectedFiniteOperatorLayer

/-!
# Selected R-cutoff detailed-construction source

This file tests the real bypass route:

`CanonicalPrimePowerRCutoffMassGrowthWindowData`
→ `DDetailedConstructionWithOperatorLegality`

It does not use `selectedClosedPayload` or `selectedH0`.
-/

namespace RHFormalization

noncomputable section

structure SelectedRCutoffDetailedConstructionSource where
  S :
    CanonicalPrimePowerRCutoffMassGrowthWindowData selectedFiniteOperatorLayer

  W :
    DCanonicalWindowData

  Wapi :
    DCanonicalWindowAPI W

  F :
    DFHLimitData selectedFiniteOperatorLayer.toStagePackage

  sectors :
    DResidualSectorData selectedFiniteOperatorLayer.toStagePackage

  sectorSplit :
    DResidualSectorSplitAPI selectedFiniteOperatorLayer.toStagePackage sectors

  sectorBounds :
    DResidualSectorBoundsAPI selectedFiniteOperatorLayer.toStagePackage sectors

  master :
    DMasterResidualAPI selectedFiniteOperatorLayer.toStagePackage sectors

  overlapBuilder :
    let Cshared := RCutoffEstimateSharedPackage selectedFiniteOperatorLayer S
    let finiteCanonicalLimit :=
      RCutoffEstimateFiniteCanonicalLimit selectedFiniteOperatorLayer S
    let Bdata :=
      buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
        selectedFiniteOperatorLayer
        Cshared
        finiteCanonicalLimit
    let Rdata := master.h_master sectorSplit sectorBounds
    DOverlapIdentityAPI
      selectedFiniteOperatorLayer.toStagePackage
      Bdata
      F
      Rdata

def buildSelectedDDetailedConstructionFromRCutoffSource
    (Src : SelectedRCutoffDetailedConstructionSource) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromRCutoffEstimate
    selectedFiniteOperatorLayer
    Src.S
    Src.W
    Src.Wapi
    Src.F
    Src.sectors
    Src.sectorSplit
    Src.sectorBounds
    Src.master
    Src.overlapBuilder

end

end RHFormalization
