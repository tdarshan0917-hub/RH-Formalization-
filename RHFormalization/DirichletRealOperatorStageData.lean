import RHFormalization.DirichletPWQOToOperatorEigenvalue
import RHFormalization.RealOperatorStageData

/-!
# RHFormalization.DirichletRealOperatorStageData

Adapter from `DirichletPWQOData` to the `RealOperatorStageData` obligation.

This does not construct the operator stage from scratch. It states the exact
stage-level realization facts needed to turn the Dirichlet PWQO spectrum into
the honest FHcan D-side.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/-- A selected finite-stage ladder realizes the Dirichlet PWQO resolvent terms. -/
structure DirichletStageRealization
    (D : DirichletPWQOData)
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer) where

  h_resolvent_term :
    ∀ n : ℕ, ∀ s : ℂ, ∀ k : ℕ,
      (S.alpha n).resolventTraceTerm s k =
        (s + (D.lamShifted k : ℂ))⁻¹

  h_F_stage_is_resolvent :
    ∀ n : ℕ, ∀ s : ℂ,
      finiteOperatorLayer.toStagePackage.F_stage (S.alpha n) s =
        ∑' k : ℕ, (S.alpha n).resolventTraceTerm s k

/-- Dirichlet stage realization gives `RealOperatorStageData` for the FHcan route. -/
def DirichletStageRealization.toRealOperatorStageData
    {D : DirichletPWQOData}
    {finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer}
    {S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer}
    (R : DirichletStageRealization D finiteOperatorLayer S) :
    RealOperatorStageData D.toOperatorEigenvalueData finiteOperatorLayer S :=
  { h_resolvent_summand := by
      intro n
      exact
        { h_term := by
            intro s k
            simpa [DirichletPWQOData.toOperatorEigenvalueData]
              using R.h_resolvent_term n s k }
    h_F_stage_is_resolvent := R.h_F_stage_is_resolvent }

/-- Dirichlet stage realization supplies the honest zero-residual D-side object. -/
def buildHonestYZeroResidualFromDirichletStageRealization
    {D : DirichletPWQOData}
    {S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        designedFiniteOperatorLayer}
    (R : DirichletStageRealization D designedFiniteOperatorLayer S) :
    DDetailedConstructionWithOperatorLegality :=
  buildHonestYZeroResidualFromRealOperatorStageData
    S
    D.toOperatorEigenvalueData
    (R.toRealOperatorStageData)

#print axioms DirichletStageRealization
#print axioms DirichletStageRealization.toRealOperatorStageData
#print axioms buildHonestYZeroResidualFromDirichletStageRealization

end

end RHFormalization
