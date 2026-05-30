import RHFormalization.AppendixDPrimePowerLimitReduction
import RHFormalization.AppendixDOperatorPrimePowerDetailedConstruction

/-!
# RHFormalization.AppendixDOperatorFiniteCanonicalDetailedConstruction

D-side constructor from the reduced finite-canonical convergence input.

This is not an RH endpoint.

It composes the already theorem-backed chain:

finite operator layer
  → finite canonical prime-power formula
  → reduced finite-canonical convergence
  → DBcanLimitData
  → DDetailedConstructionWithOperatorLegality.

After this file, the remaining D-side package-limit burden is concentrated in
`DOperatorFiniteCanonicalLimitAtOverlapData`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build the detailed Appendix-D construction with operator legality directly from
the reduced finite-canonical convergence input.

The resulting `B` field is constructed by

`buildDBcanLimitDataFromOperatorFiniteCanonicalLimit`.
-/
def buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (Cshared : CanonicalPrimePowerPackage)
    (finiteCanonicalLimit :
      DOperatorFiniteCanonicalLimitAtOverlapData
        finiteOperatorLayer
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
  let Bdata :=
    buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
      finiteOperatorLayer
      Cshared
      finiteCanonicalLimit
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
The D-side `Bcan` function in the detailed construction built from reduced
finite-canonical convergence is definitionally the shared package function.
-/
theorem detailedConstructionFromFiniteCanonicalLimit_Bcan_eq_shared
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (Cshared : CanonicalPrimePowerPackage)
    (finiteCanonicalLimit :
      DOperatorFiniteCanonicalLimitAtOverlapData
        finiteOperatorLayer
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
    (s : ℂ) :
    (buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
      finiteOperatorLayer
      Cshared
      finiteCanonicalLimit
      W
      Wapi
      F
      sectors
      sectorSplit
      sectorBounds
      master
      overlapBuilder).B.Bcan s =
        Cshared.Bshared s := by
  rfl

/--
Extract the strengthened D-side shared-package matching theorem from the detailed
construction built using reduced finite-canonical convergence.
-/
theorem detailedConstructionFromFiniteCanonicalLimit_h_Bcan_matches_shared
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (Cshared : CanonicalPrimePowerPackage)
    (finiteCanonicalLimit :
      DOperatorFiniteCanonicalLimitAtOverlapData
        finiteOperatorLayer
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
    (s : ℂ)
    (hs : s ∈ RightHalfPlane finiteOperatorLayer.toStagePackage.sigma0) :
    (buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
      finiteOperatorLayer
      Cshared
      finiteCanonicalLimit
      W
      Wapi
      F
      sectors
      sectorSplit
      sectorBounds
      master
      overlapBuilder).B.Bcan s =
        Cshared.Bshared s := by
  exact
    (buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
      finiteOperatorLayer
      Cshared
      finiteCanonicalLimit
      W
      Wapi
      F
      sectors
      sectorSplit
      sectorBounds
      master
      overlapBuilder).B.h_Bcan_matches_shared s hs

end

end RHFormalization
