import RHFormalization.AppendixDOperatorPrimePowerToDBcan

/-!
# RHFormalization.AppendixDOperatorPrimePowerDetailedConstruction

D-side constructor from operator prime-power limit data.

This is not an RH endpoint.

It removes the raw `B : DBcanLimitData ...` input from the detailed
operator-legality construction by building `B` from:

* the finite operator layer;
* the finite spike-sum/canonical prime-power formula already carried by it;
* the prime-power finite-to-limit data on the overlap half-plane.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build the detailed Appendix-D construction with operator legality from
operator-prime-power limit data.

This is the composed D-side construction:

`finiteOperatorLayer`
  → `toFiniteCanonicalPrimePowerFormula`
  → `DOperatorPrimePowerLimitAtOverlapData`
  → `DBcanLimitData`
  → `DDetailedConstructionWithOperatorLegality`.
-/
def buildDDetailedConstructionWithOperatorLegalityFromPrimePowerLimit
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (Bcan : ℂ → ℂ)
    (Cshared : CanonicalPrimePowerPackage)
    (primePowerLimit :
      DOperatorPrimePowerLimitAtOverlapData
        finiteOperatorLayer
        Bcan
        Cshared)
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
      let Bdata :=
        buildDBcanLimitDataFromOperatorPrimePowerLimit
          finiteOperatorLayer
          Bcan
          Cshared
          primePowerLimit
      let Rdata := master.h_master sectorSplit sectorBounds
      DOverlapIdentityAPI
        finiteOperatorLayer.toStagePackage
        Bdata
        F
        Rdata) :
    DDetailedConstructionWithOperatorLegality :=
  let Bdata :=
    buildDBcanLimitDataFromOperatorPrimePowerLimit
      finiteOperatorLayer
      Bcan
      Cshared
      primePowerLimit
  { finiteOperatorLayer := finiteOperatorLayer
    W := W
    Wapi := Wapi
    B := Bdata
    F := F
    sectors := sectors
    sectorSplit := sectorSplit
    sectorBounds := sectorBounds
    master := master
    overlapBuilder := overlapBuilder }

/--
Extract the D-side shared-package equality from the detailed construction built
via operator-prime-power limit data.
-/
theorem detailedConstructionFromPrimePowerLimit_h_Bcan_matches_shared
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (Bcan : ℂ → ℂ)
    (Cshared : CanonicalPrimePowerPackage)
    (primePowerLimit :
      DOperatorPrimePowerLimitAtOverlapData
        finiteOperatorLayer
        Bcan
        Cshared)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane finiteOperatorLayer.toStagePackage.sigma0) :
    Bcan s = Cshared.Bshared s :=
  operatorPrimePowerLimit_h_Bcan_matches_shared
    finiteOperatorLayer
    Bcan
    Cshared
    primePowerLimit
    s
    hs

end

end RHFormalization
