import RHFormalization.DOperatorExport

/-!
# Appendix-D stage-sequence reduction

This file does NOT add an axiom.

It proves the exact reduction needed by the current alpha/index blocker:

If Appendix D supplies certified finite stages with arbitrarily large `R`,
then the selected sequence

  alpha : ℕ → DFiniteStage

with

  ∀ n, (n : ℝ) ≤ (alpha n).R

is immediate by classical choice.
-/

namespace RHFormalization

noncomputable section

/--
No-axiom reduction: a real-valued stage-existence theorem implies the
nat-indexed stage sequence needed by the selected D-window alpha/index object.
-/
theorem appendixD_ordered_cutoff_stage_sequence_from_R_existence
    (hStage : ∀ R : ℝ, ∃ α : DFiniteStage, R ≤ α.R) :
    ∃ alpha : ℕ → DFiniteStage,
      ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R := by
  classical
  refine ⟨fun n => Classical.choose (hStage (n : ℝ)), ?_⟩
  intro n
  exact Classical.choose_spec (hStage (n : ℝ))

/--
Pointwise nat version of the same reduction.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_nat_from_R_existence
    (hStage : ∀ R : ℝ, ∃ α : DFiniteStage, R ≤ α.R)
    (n : ℕ) :
    ∃ α : DFiniteStage, (n : ℝ) ≤ α.R := by
  exact hStage (n : ℝ)

end

end RHFormalization
