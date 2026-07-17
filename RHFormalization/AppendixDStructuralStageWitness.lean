import RHFormalization.DOperatorExport
import RHFormalization.ZeroNativeStageWitness
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff

/-!
# RHFormalization.AppendixDStructuralStageWitness

A structural finite-stage witness for Appendix D.

This file constructs a `DFiniteStage` using:
* the axiom-free full-domain zero native stage,
* trivial heat/resolvent/Duhamel/mixed-word proxy data,
* direct finite active spike codes from the guarded center cutoff,
* pair-code decoding `ppDecode` for the Nat-to-prime-power map.

This is the structural witness route. It inhabits the current Lean `DFiniteStage`
API. It is not the manuscript's nontrivial Appendix-D operator construction.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

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

/-- The zero real sequence has super-polynomial decay. -/
lemma zero_superPolynomialDecay :
    SuperPolynomialDecay (fun _ : ℕ => (0 : ℝ)) := by
  intro N
  refine ⟨0, by norm_num, ?_⟩
  intro k
  simp

/--
Structural Appendix-D finite stage witness.

The active spike data are the valid prime-power codes below `Rstage`, and all
free analytic proxy sequences are chosen to be zero.
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
        exact zero_superPolynomialDecay

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

/--
Structural stage-existence theorem.

This is the theorem-shaped replacement for the current custom axiom, under the
current structural `DFiniteStage` API.
-/
theorem appendixD_exists_DFiniteStage_with_R_ge_structural
    (R₀ : ℝ) :
    ∃ α : DFiniteStage, R₀ ≤ α.R := by
  exact ⟨structuralDFiniteStage R₀, structuralDFiniteStage_ge R₀⟩

#print axioms structuralDFiniteStage
#print axioms appendixD_exists_DFiniteStage_with_R_ge_structural

end

end RHFormalization
