import RHFormalization.DOperatorExport
import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDSpikeSumExtraction

namespace RHFormalization

noncomputable section

/--
Typed skeleton for the no-axiom stage-existence theorem.

This fixes the Hilbert space as `ℂ` only to get past the previous
`CompleteSpace ?E` metavariable block and expose the real remaining fields.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_skeleton_EC
    (R0 : ℝ) :
    ∃ α : DFiniteStage, R0 ≤ α.R := by
  classical

  let R : ℝ := max R0 1
  have hR_ge_R0 : R0 ≤ R := by
    exact le_max_left R0 1
  have hR_pos : 0 < R := by
    have h1 : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le h1 (le_max_right R0 1)

  let L : ℝ := R + 1
  have hL_pos : 0 < L := by
    dsimp [L]
    linarith

  refine ⟨DFiniteStage.mk
    L
    R
    hL_pos
    hR_pos
    ℂ
    ?native
    ?heatEigenvalue
    ?heatScale
    ?h_heatScale_pos
    ?h_heatEigenvalue_linear_lower
    ?resolventTraceTerm
    ?resolventBoundConstant
    ?h_resolventBoundConstant_nonneg
    ?h_resolventTraceBound
    ?duhamelTraceNormTerm
    ?h_duhamelTraceNormTerm_nonneg
    ?duhamelMajorant
    ?h_duhamelMajorant_nonneg
    ?h_duhamelTraceNormTerm_bound
    ?h_duhamelMajorant_summable
    ?mixedWordRemainder
    ?h_mixedWordRemainder_nonneg
    ?h_mixedWordSuperPolynomialDecay
    ?diagonalSpikeActive
    ?diagonalSpikeContribution
    ?canonicalSpikeContribution
    ?h_diagonalSpikeExtraction
    ?appendixDFiniteFStage
    ?diagonalSpikeActiveIndices
    ?h_diagonalSpikeActiveIndices_active
    ?h_diagonalSpikeActiveIndices_complete
    ?diagonalSpikeToPP
    ?h_diagonalSpikeToPP_inj
    ?h_canonicalSpikeContribution_eq_weightC
    ?h_diagonalSpikeToPP_center_le_R
    ?h_diagonalSpikeToPP_complete_center_le_R,
    ?_⟩

  exact hR_ge_R0

end

end RHFormalization
