import RHFormalization.DOperatorExport
import RHFormalization.SelectedDWindowAlphaIndexData

namespace RHFormalization

noncomputable section

/--
If Appendix D supplies, for every `n`, a certified finite stage whose
`R` cutoff dominates `n`, then the selected ordered cutoff sequence required
by `SelectedDWindowAlphaIndexData` follows by classical choice.

This introduces no axiom and does not touch root.
-/
theorem appendixD_ordered_cutoff_stage_sequence_from_pointwise
    (h_stage : ∀ n : ℕ, ∃ α : DFiniteStage, (n : ℝ) ≤ α.R) :
    ∃ alpha : ℕ → DFiniteStage,
      ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R := by
  classical
  refine ⟨fun n => Classical.choose (h_stage n), ?_⟩
  intro n
  exact Classical.choose_spec (h_stage n)

/--
This is the exact remaining Appendix-D source theorem.
Do not axiom it in the final proof.
It must be proved from the ordered cutoff-stage construction / D.ADM-NET.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_nat_target
    (n : ℕ) :
    ∃ α : DFiniteStage, (n : ℝ) ≤ α.R := by
  -- Real proof target:
  -- choose finite cutoff R_n ≥ n;
  -- use Appendix D fixed-(L,R) construction;
  -- choose L large enough by D.ADM-NET;
  -- package the certified finite stage as `DFiniteStage`.
  exact ?appendixD_stage_exists

end

end RHFormalization
