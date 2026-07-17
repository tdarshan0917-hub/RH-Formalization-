import RHFormalization.DOperatorExport
import RHFormalization.ZeroNativeStageWitness

/-!
# RHFormalization.EmptyDFiniteStage

Existence proof for the designed-stage route: a fully concrete `DFiniteStage`
with no active spikes, zero transform, the zero-native operator core, and all
certificates proven. `R = 1/2 < log 2`, so every valid prime power has center
`log(p^m) ≥ log 2 > R` and the cutoff completeness certificate is vacuous.
-/

namespace RHFormalization

noncomputable section

open Complex

/-- A canonical prime-power pair as the (irrelevant) value of `toPP`. -/
noncomputable def ppTwo : PrimePowerPair := default

/-- The empty designed finite stage. -/
noncomputable def emptyDFiniteStage : DFiniteStage :=
  { L := 1
    R := 1/2
    hL_pos := one_pos
    hR_pos := by norm_num
    E := ℂ
    instNormed := inferInstance
    instInner := inferInstance
    instComplete := inferInstance
    native := zeroNativeStage
    heatEigenvalue := fun n => (n : ℝ)
    heatScale := 1
    h_heatScale_pos := one_pos
    h_heatEigenvalue_linear_lower := by intro n; simp
    resolventTraceTerm := fun _ _ => 0
    resolventBoundConstant := fun _ => 0
    h_resolventBoundConstant_nonneg := by intro s _; exact le_refl 0
    h_resolventTraceBound := by intro s _ n; simp
    duhamelTraceNormTerm := fun _ => 0
    h_duhamelTraceNormTerm_nonneg := by intro k; exact le_refl 0
    duhamelMajorant := fun _ => 0
    h_duhamelMajorant_nonneg := by intro k; exact le_refl 0
    h_duhamelTraceNormTerm_bound := by intro k; exact le_refl 0
    h_duhamelMajorant_summable := summable_zero
    mixedWordRemainder := fun _ => 0
    h_mixedWordRemainder_nonneg := by intro k; exact le_refl 0
    h_mixedWordSuperPolynomialDecay := by
      intro N
      exact ⟨0, le_refl 0, by intro k; simp⟩
    diagonalSpikeActive := fun _ => False
    diagonalSpikeContribution := fun _ => 0
    canonicalSpikeContribution := fun _ => 0
    h_diagonalSpikeExtraction := by intro q hq; exact hq.elim
    appendixDFiniteFStage := fun _ => 0
    diagonalSpikeActiveIndices := ∅
    h_diagonalSpikeActiveIndices_active := by intro q hq; simp at hq
    h_diagonalSpikeActiveIndices_complete := by intro q hq; exact hq.elim
    diagonalSpikeToPP := fun _ => ppTwo
    h_diagonalSpikeToPP_inj := by intro m hm n hn _; simp at hm
    h_canonicalSpikeContribution_eq_weightC := by intro n hn; simp at hn
    h_diagonalSpikeToPP_center_le_R := by intro n hn; simp at hn
    h_diagonalSpikeToPP_complete_center_le_R := by
      intro q hq hle
      exfalso
      have h2 : (2 : ℕ) ≤ q.natValue := by
        have hp : 2 ≤ q.p := hq.1.two_le
        have hpow : q.p ≤ q.p ^ q.m := Nat.le_self_pow hq.2.ne' q.p
        calc (2 : ℕ) ≤ q.p := hp
          _ ≤ q.p ^ q.m := hpow
          _ = q.natValue := rfl
      have h2R : (2 : ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast h2
      have hlog : Real.log 2 ≤ q.center := by
        unfold PrimePowerPair.center
        first
          | exact Real.log_le_log (by norm_num) h2R
          | exact Real.log_le_log_of_le h2R
      have hd9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith }

#print axioms emptyDFiniteStage

end

end RHFormalization
