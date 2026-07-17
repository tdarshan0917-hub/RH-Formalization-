import RHFormalization.HonestYZeroResidualFromFHcan

/-!
# RHFormalization.ResolventStageFHcanBridge

This file isolates the real remaining operator-stage obligation.

The current designed layer uses spike/displacement stages. This file defines the
condition under which a finite stage is a genuine resolvent/FHcan stage.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/-- A finite stage matches the canonical FHcan resolvent summands. -/
structure ResolventStageMatchesFHcan
    (Eop : OperatorEigenvalueData)
    (α : DFiniteStage) where
  h_term :
    ∀ s : ℂ, ∀ n : ℕ,
      α.resolventTraceTerm s n = (s + (Eop.lam n : ℂ))⁻¹

/-- The exact remaining obligation for a stage ladder: every selected stage
matches the FHcan summands. -/
structure ResolventStageLadderMatchesFHcan
    (Eop : OperatorEigenvalueData)
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S :
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
        finiteOperatorLayer) where
  h_stage :
    ∀ n : ℕ,
      ResolventStageMatchesFHcan Eop (S.alpha n)

#print axioms ResolventStageMatchesFHcan
#print axioms ResolventStageLadderMatchesFHcan

end

end RHFormalization
