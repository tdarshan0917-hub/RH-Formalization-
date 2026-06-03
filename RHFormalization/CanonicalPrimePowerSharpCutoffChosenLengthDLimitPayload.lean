import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromLimits

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayload

Final payload boundary for the selected chosen-length Appendix-D route.

All wrapper, window, inverse-speed, overlap, and residual-sector bookkeeping has
already been discharged upstream. This file names the remaining analytic payload
needed to produce

`DDetailedConstructionWithOperatorLegality`.

The remaining payload is exactly:
* selected finite operator layer;
* selected chosen-length mass-envelope package;
* limiting functions `FH` and `RH`;
* holomorphy of `FH` and `RH` on Ω;
* compact-uniform convergence of `F_stage` and `R_stage`;
* compact-uniform residual-stage bound;
* nonnegativity of the overlap half-plane parameter `sigma0`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The exact remaining analytic payload needed to close the selected chosen-length
Appendix-D construction.
-/
structure ChosenLengthDLimitPayload where
  finiteOperatorLayer :
    DFiniteStagePackageFromOperatorLayer

  S :
    CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
      finiteOperatorLayer

  FH : ℂ → ℂ
  RH : ℂ → ℂ

  h_FH_holo :
    HolomorphicOnC FH Ω

  h_RH_holo :
    HolomorphicOnC RH Ω

  h_F_stage_to_FH :
    ∀ (K : Set ℂ),
      IsCompact K →
      K ⊆ Ω →
        ∀ (ε : ℝ),
          0 < ε →
            ∀ᶠ (n : ℕ) in Filter.atTop,
              ∀ s ∈ K,
                dist
                  (finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s)
                  (FH s) < ε

  h_R_stage_to_RH :
    ∀ (K : Set ℂ),
      IsCompact K →
      K ⊆ Ω →
        ∀ (ε : ℝ),
          0 < ε →
            ∀ᶠ (n : ℕ) in Filter.atTop,
              ∀ s ∈ K,
                dist
                  (finiteOperatorLayer.toStagePackage.R_stage (S.alpha n) s)
                  (RH s) < ε

  h_R_stage_bound :
    ∀ (K : Set ℂ),
      IsCompact K →
      K ⊆ Ω →
        ∃ C, 0 ≤ C ∧
          ∀ (α : DFiniteStage), ∀ s ∈ K,
            ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C

  hσ :
    0 ≤ finiteOperatorLayer.toStagePackage.sigma0

/--
Convert the selected chosen-length D payload into the actual D-side final input
for the RH spine.
-/
def ChosenLengthDLimitPayload.toDDetailedConstructionWithOperatorLegality
    (Pld : ChosenLengthDLimitPayload) :
    DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthLimits
    Pld.finiteOperatorLayer
    Pld.S
    Pld.FH
    Pld.RH
    Pld.h_FH_holo
    Pld.h_RH_holo
    Pld.h_F_stage_to_FH
    Pld.h_R_stage_to_RH
    Pld.h_R_stage_bound
    Pld.hσ

/--
Named constructor from the final selected chosen-length D payload.
-/
def buildDDetailedConstructionWithOperatorLegalityFromChosenLengthDLimitPayload
    (Pld : ChosenLengthDLimitPayload) :
    DDetailedConstructionWithOperatorLegality :=
  Pld.toDDetailedConstructionWithOperatorLegality

end

end RHFormalization
