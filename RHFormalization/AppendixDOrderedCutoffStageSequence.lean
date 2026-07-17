import RHFormalization.DOperatorExport
import RHFormalization.SelectedDWindowAlphaIndexData

/-!
# Appendix-D ordered cutoff stage sequence

This file contains the exact no-axiom stage-sequence theorem needed by
`SelectedDWindowAlphaIndexDataInstance`.

The current Lean blocker is:
* `alpha : ℕ → DFiniteStage`
* `h_R_ge_nat : ∀ n, (n : ℝ) ≤ (alpha n).R`

The mathematical source is Appendix D's fixed finite `(L,R)` construction plus
the ordered cutoff/admissibility step: choose finite `R`, then choose `L`
large enough, and package the resulting certified finite stage.
-/

namespace RHFormalization

noncomputable section

/--
Pointwise certified finite-stage existence with arbitrarily large `R`.

This is the real theorem to prove next.
Do not replace this by an axiom in the final proof.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_nat
    (n : ℕ) :
    ∃ α : DFiniteStage, (n : ℝ) ≤ α.R := by
  /-
  Proof target.

  Mathematical plan:
  1. Let Rn : ℝ := (n : ℝ) + 1.
  2. Use the fixed finite `(L,Rn)` Appendix-D construction.
  3. Choose L large enough by the ordered cutoff/admissibility construction.
  4. Package the certified finite stage as `DFiniteStage`.
  5. Its R-field is Rn or at least ≥ n.

  The needed source is a certified finite-stage constructor theorem,
  not `DFiniteStage.mk` by hand.
  -/
  exact ?appendixD_stage_exists

/--
Once pointwise stage existence is proved, the ordered sequence follows by choice.
-/
theorem appendixD_ordered_cutoff_stage_sequence :
    ∃ alpha : ℕ → DFiniteStage,
      ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R := by
  classical
  refine
    ⟨fun n => Classical.choose
        (appendixD_exists_DFiniteStage_with_R_ge_nat n), ?_⟩
  intro n
  exact Classical.choose_spec
    (appendixD_exists_DFiniteStage_with_R_ge_nat n)

/--
The selected alpha sequence needed downstream.
-/
noncomputable def selectedDWindowStageAlpha :
    ℕ → DFiniteStage :=
  Classical.choose appendixD_ordered_cutoff_stage_sequence

/--
The selected R-growth proof needed downstream.
-/
theorem selectedDWindowStageAlpha_h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (selectedDWindowStageAlpha n).R :=
  Classical.choose_spec appendixD_ordered_cutoff_stage_sequence

end

end RHFormalization
