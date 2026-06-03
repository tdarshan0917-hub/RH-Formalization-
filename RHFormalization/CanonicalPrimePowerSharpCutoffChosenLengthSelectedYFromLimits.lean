import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromLimits

Chosen-length Appendix-D constructor reduced to raw aligned FH/RH limit data.

This file packages the remaining F/R construction step using
`buildDFHLimitDataFromCompactUniform` and
`buildDMasterResidualDataFromCompactUniform`.

After this file, the selected-D input list is reduced to:
* `FH`;
* `RH`;
* holomorphy of `FH` and `RH`;
* compact-uniform convergence of `F_stage` and `R_stage` along `S.alpha`;
* compact-uniform residual stage bound;
* sigma nonnegativity.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the chosen-length sharp-cutoff detailed D construction directly from
aligned FH/RH limit functions and their compact-uniform convergence data.
-/
def buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthLimits
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (FH RH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s)
                    (FH s) < ε)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ s ∈ K,
                  dist
                    (finiteOperatorLayer.toStagePackage.R_stage (S.alpha n) s)
                    (RH s) < ε)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
          ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
            ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0) :
    DDetailedConstructionWithOperatorLegality :=
  let F : DFHLimitData finiteOperatorLayer.toStagePackage :=
    buildDFHLimitDataFromCompactUniform
      finiteOperatorLayer.toStagePackage
      S.alpha
      FH
      h_FH_holo
      h_F_stage_to_FH

  let R : DMasterResidualData finiteOperatorLayer.toStagePackage :=
    buildDMasterResidualDataFromCompactUniform
      finiteOperatorLayer.toStagePackage
      S.alpha
      RH
      h_RH_holo
      h_R_stage_to_RH

  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed
    finiteOperatorLayer
    S
    F
    R
    h_R_stage_bound
    hσ
    (by rfl)
    (by rfl)

end

end RHFormalization
