import RHFormalization.AppendixDRCutoffEstimateDetailedConstruction
import RHFormalization.AppendixESharedPackageFunctionalCompatibility

/-!
# RHFormalization.FinalRHFromRCutoffEstimate

Current frontier theorem.

This file is not a new proof shortcut.

It records the current formalized dependency frontier after the Appendix-D
R-cutoff / mass-growth / window-error package has been wired into the detailed
D construction.

After this theorem, the remaining work is to construct the inputs:
* the R-cutoff D estimate package;
* the H-side meromorphic package;
* the function-level shared-package compatibility.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The detailed D construction produced by the current sharpest R-cutoff estimate
package.
-/
abbrev detailedConstructionFromRCutoffEstimate
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffMassGrowthWindowData finiteOperatorLayer)
    (W : DCanonicalWindowData)
    (Wapi : DCanonicalWindowAPI W)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (sectors : DResidualSectorData finiteOperatorLayer.toStagePackage)
    (sectorSplit :
      DResidualSectorSplitAPI finiteOperatorLayer.toStagePackage sectors)
    (sectorBounds :
      DResidualSectorBoundsAPI finiteOperatorLayer.toStagePackage sectors)
    (master :
      DMasterResidualAPI finiteOperatorLayer.toStagePackage sectors)
    (overlapBuilder :
      let Cshared := RCutoffEstimateSharedPackage finiteOperatorLayer S
      let finiteCanonicalLimit :=
        RCutoffEstimateFiniteCanonicalLimit finiteOperatorLayer S
      let Bdata :=
        buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
          finiteOperatorLayer
          Cshared
          finiteCanonicalLimit
      let Rdata := master.h_master sectorSplit sectorBounds
      DOverlapIdentityAPI
        finiteOperatorLayer.toStagePackage
        Bdata
        F
        Rdata) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromRCutoffEstimate
    finiteOperatorLayer
    S
    W
    Wapi
    F
    sectors
    sectorSplit
    sectorBounds
    master
    overlapBuilder

/--
Current RH frontier theorem.

If the D-side R-cutoff estimate package is supplied and the H-side package is
functionally compatible with the same shared canonical package, then the final
RH spine closes.

This theorem makes the remaining formal obligations explicit.
-/
theorem finalRHSpine_from_RCutoffEstimateData
    (ZF : ZetaZeroFacts)
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffMassGrowthWindowData finiteOperatorLayer)
    (W : DCanonicalWindowData)
    (Wapi : DCanonicalWindowAPI W)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (sectors : DResidualSectorData finiteOperatorLayer.toStagePackage)
    (sectorSplit :
      DResidualSectorSplitAPI finiteOperatorLayer.toStagePackage sectors)
    (sectorBounds :
      DResidualSectorBoundsAPI finiteOperatorLayer.toStagePackage sectors)
    (master :
      DMasterResidualAPI finiteOperatorLayer.toStagePackage sectors)
    (overlapBuilder :
      let Cshared := RCutoffEstimateSharedPackage finiteOperatorLayer S
      let finiteCanonicalLimit :=
        RCutoffEstimateFiniteCanonicalLimit finiteOperatorLayer S
      let Bdata :=
        buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
          finiteOperatorLayer
          Cshared
          finiteCanonicalLimit
      let Rdata := master.h_master sectorSplit sectorBounds
      DOverlapIdentityAPI
        finiteOperatorLayer.toStagePackage
        Bdata
        F
        Rdata)
    (X : HMeromorphicWithNormalFormPoles)
    (Compat :
      AppendixESharedPackageFunctionalCompatibility
        (detailedConstructionFromRCutoffEstimate
          finiteOperatorLayer
          S
          W
          Wapi
          F
          sectors
          sectorSplit
          sectorBounds
          master
          overlapBuilder)
        X) :
    RiemannHypothesis :=
  finalRHSpine_after_sharedPackageFunctionalCompatibility
    ZF
    (detailedConstructionFromRCutoffEstimate
      finiteOperatorLayer
      S
      W
      Wapi
      F
      sectors
      sectorSplit
      sectorBounds
      master
      overlapBuilder)
    X
    Compat

end

end RHFormalization
