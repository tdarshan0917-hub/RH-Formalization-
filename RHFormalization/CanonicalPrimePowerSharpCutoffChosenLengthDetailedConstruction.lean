import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.AppendixDOperatorFiniteCanonicalDetailedConstruction

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDetailedConstruction

Wires chosen-length sharp-cutoff mass-envelope data into the D detailed
construction package.

This promotes the already-proved chosen-length route:

  chosen length → massEnvelope/windowSpeed → 0
  chosen length → exhaustion data
  chosen length → DBcan limit data

into:

  DDetailedConstructionWithOperatorLegality.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The shared canonical prime-power package attached to chosen-length sharp-cutoff
data.
-/
abbrev SharpCutoffChosenLengthSharedPackage
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer) :
    CanonicalPrimePowerPackage :=
  canonicalPrimePowerPackageFromKernelTsum
    finiteOperatorLayer.toStagePackage.sigma0
    S.Kshared

/--
The finite-canonical-limit object exported from chosen-length sharp-cutoff data.
-/
abbrev SharpCutoffChosenLengthFiniteCanonicalLimit
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer) :
    DOperatorFiniteCanonicalLimitAtOverlapData
      finiteOperatorLayer
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S) :=
  S.toExhaustionData.toDOperatorFiniteCanonicalLimit

/--
Build the D detailed construction from chosen-length sharp-cutoff mass-envelope
data.

This is the selected D-side wiring layer:

  chosen-length data
    → finite-canonical-limit data
    → DDetailedConstructionWithOperatorLegality.
-/
def buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthMassEnvelope
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (W : DCanonicalWindowData)
    (Wapi : DCanonicalWindowAPI W)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (sectors : DResidualSectorData finiteOperatorLayer.toStagePackage)
    (sectorSplit : DResidualSectorSplitAPI finiteOperatorLayer.toStagePackage sectors)
    (sectorBounds : DResidualSectorBoundsAPI finiteOperatorLayer.toStagePackage sectors)
    (master : DMasterResidualAPI finiteOperatorLayer.toStagePackage sectors)
    (overlapBuilder :
      let Cshared :=
        SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S
      have finiteCanonicalLimit :=
        SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S
      have Bdata :=
        buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
          finiteOperatorLayer
          Cshared
          finiteCanonicalLimit
      have Rdata := master.h_master sectorSplit sectorBounds
      DOverlapIdentityAPI finiteOperatorLayer.toStagePackage Bdata F Rdata) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
    finiteOperatorLayer
    (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
    (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)
    W
    Wapi
    F
    sectors
    sectorSplit
    sectorBounds
    master
    overlapBuilder

end

end RHFormalization
