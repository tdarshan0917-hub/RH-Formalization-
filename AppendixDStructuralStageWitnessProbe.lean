import RHFormalization.DOperatorExport
import RHFormalization.ZeroNativeStageWitness
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

#check zeroNativeStage
#check activePrimePowerCodesCenterBelow
#check centerCutoffSpikeActive
#check centerCutoffSpikeActive_sound
#check centerCutoffSpikeActive_complete
#check activePrimePowerCodesCenterBelow_toPP_inj
#check activePrimePowerCodesCenterBelow_center_le_R
#check activePrimePowerCodesCenterBelow_complete
#check SuperPolynomialDecay
#check summable_zero

/-- Structural cutoff used for a requested lower bound. -/
noncomputable def structuralStageR (R₀ : ℝ) : ℝ :=
  max R₀ 1

lemma structuralStageR_pos (R₀ : ℝ) :
    0 < structuralStageR R₀ := by
  unfold structuralStageR
  exact lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1)

lemma structuralStageR_ge (R₀ : ℝ) :
    R₀ ≤ structuralStageR R₀ := by
  unfold structuralStageR
  exact le_max_left R₀ 1

/-- Probe: zero sequence has super-polynomial decay. -/
example : SuperPolynomialDecay (fun _ : ℕ => (0 : ℝ)) := by
  simp [SuperPolynomialDecay]

/--
First structural Appendix-D finite stage witness.

This is the structural witness route: native operator is the full-domain zero
native stage, and the prime-power active indices are supplied by the direct
center-cutoff pair-code construction.
-/
noncomputable def structuralDFiniteStage (R₀ : ℝ) : DFiniteStage := by
  classical
  let Rstage : ℝ := structuralStageR R₀

  refine
    { L := 1
      R := Rstage
      hL_pos := by norm_num
      hR_pos := by
        dsimp [Rstage]
        exact structuralStageR_pos R₀

      E := ℂ
      instNormed := inferInstance
      instInner := inferInstance
      instComplete := inferInstance
      native := zeroNativeStage

      heatEigenvalue := fun n : ℕ => (n : ℝ)
      heatScale := 1
      h_heatScale_pos := by norm_num
      h_heatEigenvalue_linear_lower := by
        intro n
        simp

      resolventTraceTerm := fun _s _n => 0
      resolventBoundConstant := fun _s => 0
      h_resolventBoundConstant_nonneg := by
        intro s hs
        simp
      h_resolventTraceBound := by
        intro s hs n
        simp

      duhamelTraceNormTerm := fun _k => 0
      h_duhamelTraceNormTerm_nonneg := by
        intro k
        simp
      duhamelMajorant := fun _k => 0
      h_duhamelMajorant_nonneg := by
        intro k
        simp
      h_duhamelTraceNormTerm_bound := by
        intro k
        simp
      h_duhamelMajorant_summable := by
        simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

      mixedWordRemainder := fun _k => 0
      h_mixedWordRemainder_nonneg := by
        intro k
        simp
      h_mixedWordSuperPolynomialDecay := by
        simp [SuperPolynomialDecay]

      diagonalSpikeActive := centerCutoffSpikeActive Rstage
      diagonalSpikeContribution := fun n => PrimePowerPair.weightC (ppDecode n)
      canonicalSpikeContribution := fun n => PrimePowerPair.weightC (ppDecode n)
      h_diagonalSpikeExtraction := by
        intro n hn
        rfl

      appendixDFiniteFStage := fun _s => 0

      diagonalSpikeActiveIndices := activePrimePowerCodesCenterBelow Rstage
      h_diagonalSpikeActiveIndices_active := by
        intro n hn
        exact centerCutoffSpikeActive_sound Rstage n hn
      h_diagonalSpikeActiveIndices_complete := by
        intro n hn
        exact centerCutoffSpikeActive_complete Rstage n hn

      diagonalSpikeToPP := ppDecode
      h_diagonalSpikeToPP_inj := by
        intro m hm n hn hmn
        exact activePrimePowerCodesCenterBelow_toPP_inj Rstage m hm n hn hmn
      h_canonicalSpikeContribution_eq_weightC := by
        intro n hn
        rfl
      h_diagonalSpikeToPP_center_le_R := by
        intro n hn
        exact activePrimePowerCodesCenterBelow_center_le_R Rstage n hn
      h_diagonalSpikeToPP_complete_center_le_R := by
        intro q hqvalid hqcenter
        exact activePrimePowerCodesCenterBelow_complete Rstage q hqvalid hqcenter }

theorem structuralDFiniteStage_ge (R₀ : ℝ) :
    R₀ ≤ (structuralDFiniteStage R₀).R := by
  dsimp [structuralDFiniteStage]
  exact structuralStageR_ge R₀

theorem appendixD_exists_DFiniteStage_with_R_ge_structural
    (R₀ : ℝ) :
    ∃ α : DFiniteStage, R₀ ≤ α.R := by
  exact ⟨structuralDFiniteStage R₀, structuralDFiniteStage_ge R₀⟩

#print axioms structuralDFiniteStage
#print axioms appendixD_exists_DFiniteStage_with_R_ge_structural

end

end RHFormalization
