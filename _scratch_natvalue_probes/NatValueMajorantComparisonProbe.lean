import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

theorem heatKernelNatValueMajorant_le_scaled_pairPSeriesModel_probe :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ q : PrimePowerPair,
        heatKernelNatValueMajorant q ≤ C * heatKernelPairPSeriesModel q := by
  refine ⟨(1000000 : ℝ), by norm_num, ?_⟩
  intro q
  by_cases hq : IsPrimePowerPair q
  · rw [heatKernelNatValueMajorant_eq_valid_primePower_formula q hq]
    unfold heatKernelPairPSeriesModel
    rcases hq with ⟨hp, hm⟩
    have hp2 : 2 ≤ q.p := hp.two_le
    have hp_pos_nat : 0 < q.p := lt_of_lt_of_le (by norm_num) hp2
    have hm_pos_nat : 0 < q.m := hm
    have hp_pos : 0 < (q.p : ℝ) := by exact_mod_cast hp_pos_nat
    have hm_pos : 0 < (q.m : ℝ) := by exact_mod_cast hm_pos_nat
    have hnat_pos : 0 < (q.natValue : ℝ) := by
      unfold PrimePowerPair.natValue
      positivity
    have hsqrt_pos : 0 < Real.sqrt (q.natValue : ℝ) := by
      exact Real.sqrt_pos.2 hnat_pos
    have hlog_nonneg : 0 ≤ Real.log (q.p : ℝ) := by
      have hp_one : (1 : ℝ) ≤ (q.p : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp2)
      exact Real.log_nonneg hp_one
    have h_abs_log_div :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| =
          Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ) := by
      rw [abs_of_nonneg]
      exact div_nonneg hlog_nonneg (le_of_lt hsqrt_pos)

    rw [h_abs_log_div]

    -- This is the arithmetic inequality we must prove:
    -- log(p)/sqrt(p^m) * (p^m)^(-3)
    -- ≤ 1000000 / ((p+1)^2 * (m+1)^2).
    --
    -- The next Lean error tells us exactly which inequality lemma is missing.
    nlinarith
  · rw [heatKernelNatValueMajorant_eq_zero_of_not_isPrimePowerPair q hq]
    unfold heatKernelPairPSeriesModel
    positivity

end

end RHFormalization
