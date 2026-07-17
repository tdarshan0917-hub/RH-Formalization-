import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromLimits
import RHFormalization.OperatorEigenvalueData

/-!
# RHFormalization.HonestYFromFHcan

Locks the correct Appendix-D route:

* `FH := Eop.FHcan`
* `h_FH_holo := Eop.FHcan_holo`

After this file, the only remaining D-side bridge is the honest convergence input:

`finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) → Eop.FHcan`

No displacement-kernel principal-part route is used here.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

def buildHonestYFromFHcan
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer)
    (Eop : OperatorEigenvalueData)
    (RH : ℂ → ℂ)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FHcan :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.F_stage
                      (S.alpha n) s)
                    (Eop.FHcan s) < ε)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.R_stage
                      (S.alpha n) s)
                    (RH s) < ε)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
            ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthLimits
    finiteOperatorLayer
    S
    Eop.FHcan
    RH
    (OperatorEigenvalueData.FHcan_holo Eop)
    h_RH_holo
    h_F_stage_to_FHcan
    h_R_stage_to_RH
    h_R_stage_bound
    hσ

#print axioms buildHonestYFromFHcan

end

end RHFormalization
