import RHFormalization.AppendixDStructuralStageWitness

/-!
# RHFormalization.AppendixDStageExistenceAssumption

The former Appendix-D stage-existence assumption is now discharged by the
structural finite-stage witness.

This proves the same exported theorem name previously supplied as a custom axiom:

  appendixD_exists_DFiniteStage_with_R_ge :
    ∀ R : ℝ, ∃ α : DFiniteStage, R ≤ α.R

under the current `DFiniteStage` API.
-/

namespace RHFormalization

noncomputable section

/--
For every real cutoff `R`, there exists a certified finite Appendix-D stage
whose stage cutoff is at least `R`.

This replaces the former custom axiom with the structural witness theorem.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge
    (R : ℝ) :
    ∃ α : DFiniteStage, R ≤ α.R :=
  appendixD_exists_DFiniteStage_with_R_ge_structural R

#print axioms appendixD_exists_DFiniteStage_with_R_ge

end

end RHFormalization
