import RHFormalization.SelectedFiniteOperatorLayer
import RHFormalization.AppendixDSpikeCutoffCompatibility

/-!
# Selected D-window stage sequence

The index fields are already closed by `AppendixDSpikeCutoffCompatibility`.
The only remaining proof obligation is existence of certified finite stages
with arbitrarily large `R`.
-/

namespace RHFormalization

noncomputable section

structure SelectedDWindowStageSequence where
  alpha : ℕ → DFiniteStage
  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

/--
The real remaining theorem.

This is the exact finite-stage existence statement needed to finish the
alpha/index package. It must be proved from the manuscript's finite-stage
construction.

Do not prove this by constructing `DFiniteStage.mk` by hand unless the
manuscript gives all certificates required by that constructor.
-/
theorem exists_DFiniteStage_with_R_ge_nat :
    ∀ n : ℕ, ∃ α : DFiniteStage, (n : ℝ) ≤ α.R := by
  intro n
  -- This is the actual remaining proof.
  -- It must come from the Appendix-D finite-stage construction:
  -- for every cutoff n, build/select a certified finite stage α with R ≥ n.
  exact ?exists_stage_with_R_ge_n

/--
Package the selected stage sequence by choice from
`exists_DFiniteStage_with_R_ge_nat`.
-/
def selectedDWindowStageSequence :
    SelectedDWindowStageSequence :=
by
  classical
  refine
  {
    alpha := fun n => Classical.choose (exists_DFiniteStage_with_R_ge_nat n)
    h_R_ge_nat := ?_
  }
  intro n
  exact Classical.choose_spec (exists_DFiniteStage_with_R_ge_nat n)

end

end RHFormalization
