import RHFormalization.DOperatorExport
import RHFormalization.AppendixDStageSequenceReduction

/-!
# Appendix D stage existence from the manuscript

This is the current no-axiom formalization frontier.

The no-axiom reduction is already built:

  appendixD_ordered_cutoff_stage_sequence_from_R_existence

So the only remaining source theorem is:

  ∀ R : ℝ, ∃ α : DFiniteStage, R ≤ α.R

This file does not add an axiom.
-/

namespace RHFormalization

noncomputable section

/--
Certified finite Appendix-D stage existence with arbitrary R lower bound.

This is the real theorem to prove from the finite `(L,R)` Appendix-D stage
construction.

Mathematical source:
* finite cutoff `R`;
* choose admissible finite window/stage data;
* package the certified stage as `DFiniteStage`;
* prove its `R` field dominates the requested lower bound.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge
    (R : ℝ) :
    ∃ α : DFiniteStage, R ≤ α.R := by
  -- REAL PROOF GOES HERE.
  -- Do not replace this theorem by an axiom in the final formalization.
  exact ?appendixD_stage_exists_for_R

/--
Nat-indexed version needed by the selected alpha/index object.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_nat
    (n : ℕ) :
    ∃ α : DFiniteStage, (n : ℝ) ≤ α.R := by
  exact appendixD_exists_DFiniteStage_with_R_ge (n : ℝ)

/--
Once the source theorem is proved, the selected stage sequence follows from
the already-built no-axiom reduction lemma.
-/
theorem appendixD_ordered_cutoff_stage_sequence :
    ∃ alpha : ℕ → DFiniteStage,
      ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R := by
  exact appendixD_ordered_cutoff_stage_sequence_from_R_existence
    appendixD_exists_DFiniteStage_with_R_ge

end

end RHFormalization
