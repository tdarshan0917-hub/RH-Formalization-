import RHFormalization.DOperatorExport
import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDSpikeSumExtraction

namespace RHFormalization

noncomputable section

/--
This is the real no-axiom frontier.

The goal is not another search. The goal is to construct one certified
`DFiniteStage` with cutoff at least `R`.

This skeleton deliberately exposes the exact fields Lean still needs.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_skeleton
    (R0 : ℝ) :
    ∃ α : DFiniteStage, R0 ≤ α.R := by
  classical

  -- Choose a stage cutoff. This part is easy.
  let R : ℝ := max R0 1
  have hR_ge_R0 : R0 ≤ R := by
    exact le_max_left R0 1
  have hR_pos : 0 < R := by
    have h1 : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le h1 (le_max_right R0 1)

  -- Choose a window length. This is only a placeholder until D.ADM-NET is formalized.
  let L : ℝ := R + 1
  have hL_pos : 0 < L := by
    dsimp [L]
    linarith

  /-
  The following `refine` is intentionally not completed.
  It will print the exact remaining constructor obligations for `DFiniteStage.mk`.

  This tells us whether the missing pieces are:
    - native operator construction,
    - heat eigenvalue bounds,
    - resolvent bounds,
    - Duhamel bounds,
    - mixed-word decay,
    - diagonal spike extraction,
    - active index finiteness,
    - prime-power cutoff completeness.
  -/
  refine ⟨DFiniteStage.mk
    L
    R
    hL_pos
    hR_pos
    ?E
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

  -- This last goal should be easy once the stage is constructed.
  exact hR_ge_R0

end

end RHFormalization
