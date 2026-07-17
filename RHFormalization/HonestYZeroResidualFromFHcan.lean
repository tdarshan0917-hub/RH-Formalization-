import RHFormalization.HonestYFromFHcan
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope

/-!
# RHFormalization.HonestYZeroResidualFromFHcan

Specializes `buildHonestYFromFHcan` to the designed zero-residual layer.

This file locks the remaining operator-side obligation to exactly one theorem:

`h_F_stage_to_FHcan`.

Everything else is zero residual / already banked.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

def buildHonestYZeroResidualFromFHcan
    (S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        designedFiniteOperatorLayer)
    (Eop : OperatorEigenvalueData)
    (h_F_stage_to_FHcan :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (designedFiniteOperatorLayer.toStagePackage.F_stage
                      (S.alpha n) s)
                    (Eop.FHcan s) < ε) :
    DDetailedConstructionWithOperatorLegality :=
  buildHonestYFromFHcan
    designedFiniteOperatorLayer
    S
    Eop
    (fun _ => 0)
    (holomorphicOnC_const 0 Ω)
    h_F_stage_to_FHcan
    (by
      intro K hK hKOmega ε hε
      filter_upwards with n s hs
      rw [designedFiniteOperatorLayer_R_stage_eq_zero]
      simpa [dist_self] using hε)
    designedFiniteOperatorLayer_R_stage_bound
    (by
      simpa [designedFiniteOperatorLayer_sigma0])

#print axioms buildHonestYZeroResidualFromFHcan

end

end RHFormalization
