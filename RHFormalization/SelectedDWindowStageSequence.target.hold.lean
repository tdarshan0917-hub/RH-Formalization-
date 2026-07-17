import RHFormalization.SelectedDWindowAlphaIndexData

namespace RHFormalization

noncomputable section

/--
Selected Appendix-D finite stage sequence.

This is the remaining non-circular alpha/R-growth theorem:
for every `n`, choose a certified finite stage whose prime-power cutoff
dominates `n`.
-/
structure SelectedDWindowStageSequence where
  alpha : ℕ → DFiniteStage
  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

/--
The actual missing theorem.

This must be proved from the Appendix-D finite cutoff/window construction.
Do not fill this by a downstream record, factor-bounds object, or selectedY route.
-/
def selectedDWindowStageSequence :
    SelectedDWindowStageSequence :=
by
  -- PROOF NEEDED FROM MANUSCRIPT:
  -- construct `alpha n : DFiniteStage` with `(n : ℝ) ≤ (alpha n).R`.
  --
  -- If there is no manuscript construction of certified finite stages
  -- with arbitrarily large R, this route cannot close without adding
  -- an assumption.
  refine
  {
    alpha := ?alpha
    h_R_ge_nat := ?h_R_ge_nat
  }

end

end RHFormalization
