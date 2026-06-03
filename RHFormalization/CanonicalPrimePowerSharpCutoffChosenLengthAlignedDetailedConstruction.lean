import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthOverlapBuilder
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDetailedConstruction

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthAlignedDetailedConstruction

Final chosen-length D-side constructor under aligned-input hypotheses.

This file packages the chosen-length sharp-cutoff mass-envelope route into a
`DDetailedConstructionWithOperatorLegality`, using the already-proved aligned
overlap builder.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the chosen-length sharp-cutoff detailed Appendix-D construction from
aligned F/R limit data.

This is the clean D-side wrapper immediately before producing a concrete
`selectedY`.
-/
def buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthAligned
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
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
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha :
      (master.h_master sectorSplit sectorBounds).alpha = S.alpha) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthMassEnvelope
    finiteOperatorLayer
    S
    W
    Wapi
    F
    sectors
    sectorSplit
    sectorBounds
    master
    (chosenLengthOverlapBuilder_of_alpha_aligned
      finiteOperatorLayer
      S
      F
      sectors
      sectorSplit
      sectorBounds
      master
      hσ
      hF_alpha
      hR_alpha)

end

end RHFormalization
