import RHFormalization.HonestYZeroResidualFromFHcan
import RHFormalization.ResolventStageFHcanBridge

/-!
# RHFormalization.RealOperatorStageData

This file isolates the exact non-scaffold operator-stage obligation.

A genuine close requires a stage ladder whose exported finite transform is the
resolvent trace and whose resolvent summands match `FHcan`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/-- The honest realization condition: the finite stages really carry the
canonical FHcan resolvent summands. -/
structure RealOperatorStageData
    (Eop : OperatorEigenvalueData)
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer) where

  /-- Each selected stage's resolvent summand is the FHcan summand. -/
  h_resolvent_summand :
    ∀ n : ℕ,
      ResolventStageMatchesFHcan Eop (S.alpha n)

  /-- The exported finite transform is the stage resolvent trace package. -/
  h_F_stage_is_resolvent :
    ∀ n : ℕ, ∀ s : ℂ,
      finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s =
        ∑' k : ℕ, (S.alpha n).resolventTraceTerm s k

/-- Real operator stage data gives the ladder-level FHcan summand match. -/
def RealOperatorStageData.toResolventStageLadderMatchesFHcan
    {Eop : OperatorEigenvalueData}
    {finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer}
    {S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer}
    (R : RealOperatorStageData Eop finiteOperatorLayer S) :
    ResolventStageLadderMatchesFHcan Eop finiteOperatorLayer S :=
  { h_stage := R.h_resolvent_summand }

/-- Real operator stage data gives the exact compact-uniform convergence input
needed by `buildHonestYFromFHcan`: in fact the stages are pointwise equal to
`FHcan`, so the compact-uniform estimate is immediate. -/
theorem RealOperatorStageData.h_F_stage_to_FHcan
    {Eop : OperatorEigenvalueData}
    {finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer}
    {S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer}
    (R : RealOperatorStageData Eop finiteOperatorLayer S) :
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
                  (Eop.FHcan s) < ε := by
  intro K hK hKOmega ε hε
  filter_upwards with n
  intro s hs

  have hstage :
      finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s =
        ∑' k : ℕ, (S.alpha n).resolventTraceTerm s k :=
    R.h_F_stage_is_resolvent n s

  have hsum :
      (∑' k : ℕ, (S.alpha n).resolventTraceTerm s k) =
        ∑' k : ℕ, (s + (Eop.lam k : ℂ))⁻¹ := by
    apply tsum_congr
    intro k
    exact (R.h_resolvent_summand n).h_term s k

  have hEq :
      finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s =
        Eop.FHcan s := by
    calc
      finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s
          = ∑' k : ℕ, (S.alpha n).resolventTraceTerm s k := hstage
      _ = ∑' k : ℕ, (s + (Eop.lam k : ℂ))⁻¹ := hsum
      _ = Eop.FHcan s := rfl

  rw [hEq]
  simpa [dist_self] using hε

/-- For the designed zero-residual layer, real operator stage data supplies the
only remaining `FHcan` convergence input. -/
def buildHonestYZeroResidualFromRealOperatorStageData
    (S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        designedFiniteOperatorLayer)
    (Eop : OperatorEigenvalueData)
    (R : RealOperatorStageData Eop designedFiniteOperatorLayer S) :
    DDetailedConstructionWithOperatorLegality :=
  buildHonestYZeroResidualFromFHcan
    S
    Eop
    (RealOperatorStageData.h_F_stage_to_FHcan R)

#print axioms RealOperatorStageData
#print axioms RealOperatorStageData.toResolventStageLadderMatchesFHcan
#print axioms RealOperatorStageData.h_F_stage_to_FHcan
#print axioms buildHonestYZeroResidualFromRealOperatorStageData

end

end RHFormalization
