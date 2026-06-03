import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthAlignedDetailedConstruction
import RHFormalization.DResidualBulkSectorHelpers

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromFR

Chosen-length Appendix-D constructor reduced to aligned `F` and `R` limit data.

This file removes residual-sector bookkeeping from the selected D route by using
the bulk-sector helper. The remaining nontrivial inputs are now the selected
window package, selected F/R limit data, sigma nonnegativity, alpha alignment,
and a compact-uniform bound for the finite-stage residual.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build a chosen-length sharp-cutoff detailed D construction from aligned F/R
limit data, using the bulk residual sector package.

This is the clean pre-`selectedY` constructor.
-/
def buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthFR
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (W : DCanonicalWindowData)
    (Wapi : DCanonicalWindowAPI W)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (R : DMasterResidualData finiteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthAligned
    finiteOperatorLayer
    S
    W
    Wapi
    F
    (residualBulkSectorData finiteOperatorLayer.toStagePackage)
    (residualBulkSectorSplitAPI finiteOperatorLayer.toStagePackage)
    (residualBulkSectorBoundsAPI_of_R_stage_bound
      finiteOperatorLayer.toStagePackage
      h_R_stage_bound)
    (masterResidualAPI_from_data R)
    hσ
    hF_alpha
    (by
      simpa [masterResidualAPI_from_data] using hR_alpha)

end

end RHFormalization
