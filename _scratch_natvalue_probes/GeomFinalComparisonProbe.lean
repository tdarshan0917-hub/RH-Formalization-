import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

theorem heatKernelNatValueMajorant_le_scaled_pairGeomModel_probe :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ q : PrimePowerPair,
        heatKernelNatValueMajorant q ≤ C * heatKernelPairGeomModel q := by
  refine ⟨8, by norm_num, ?_⟩
  intro q
  by_cases hq : IsPrimePowerPair q
  · rw [heatKernelNatValueMajorant_eq_valid_primePower_formula q hq]
    rcases hq with ⟨hp, hm⟩

    have hp2 : 2 ≤ q.p := hp.two_le
    have hp_pos_nat : 0 < q.p := lt_of_lt_of_le (by norm_num) hp2

    have hnat_pos : 0 < (q.natValue : ℝ) := by
      unfold PrimePowerPair.natValue
      positivity

    have h_one_le_n : (1 : ℝ) ≤ (q.natValue : ℝ) := by
      exact_mod_cast (Nat.one_le_pow q.m q.p hp_pos_nat)

    have hsqrt_nonneg : 0 ≤ Real.sqrt (q.natValue : ℝ) := by
      positivity

    have hsqrt_sq :
        (Real.sqrt (q.natValue : ℝ)) ^ 2 = (q.natValue : ℝ) := by
      exact Real.sq_sqrt (by positivity)

    have hsqrt_ge_one : 1 ≤ Real.sqrt (q.natValue : ℝ) := by
      nlinarith [hsqrt_sq, h_one_le_n, hsqrt_nonneg]

    have hsqrt_pos : 0 < Real.sqrt (q.natValue : ℝ) := by
      exact Real.sqrt_pos.2 hnat_pos

    have hlog_nonneg : 0 ≤ Real.log (q.p : ℝ) := by
      have hp_one : (1 : ℝ) ≤ (q.p : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp2)
      exact Real.log_nonneg hp_one

    have h_abs :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| =
          Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ) := by
      exact abs_of_nonneg (div_nonneg hlog_nonneg (le_of_lt hsqrt_pos))

    have h_inv_sqrt_le_one :
        (Real.sqrt (q.natValue : ℝ))⁻¹ ≤ 1 := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsqrt_ge_one)

    have h_div_le_log :
        Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ) ≤
          Real.log (q.p : ℝ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left h_inv_sqrt_le_one hlog_nonneg

    have hlog_le_p : Real.log (q.p : ℝ) ≤ (q.p : ℝ) := by
      exact Real.log_le_self (by positivity)

    have habs_le_p :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| ≤
          (q.p : ℝ) := by
      rw [h_abs]
      exact le_trans h_div_le_log hlog_le_p

    have hmajor_part :
        |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| *
            ((q.natValue : ℝ) ^ 3)⁻¹
          ≤ (q.p : ℝ) * ((q.natValue : ℝ) ^ 3)⁻¹ := by
      exact mul_le_mul_of_nonneg_right habs_le_p (by positivity)

    have hpabs : |(q.p : ℝ) + 1| = (q.p : ℝ) + 1 := by
      exact abs_of_nonneg (by positivity)

    have hnum :
        (q.p : ℝ) * ((q.p : ℝ) + 1)^2 * (2 : ℝ)^q.m
          ≤ 8 * (q.natValue : ℝ)^3 :=
      geom_numerator_bound_natValue q hp2 hm

    have htarget :
        (q.p : ℝ) * ((q.natValue : ℝ) ^ 3)⁻¹
          ≤ 8 * heatKernelPairGeomModel q := by
      unfold heatKernelPairGeomModel
      rw [hpabs]

      have hp1_ne : ((q.p : ℝ) + 1) ≠ 0 := by positivity
      have hp1_sq_ne : ((q.p : ℝ) + 1)^2 ≠ 0 := by
        exact pow_ne_zero 2 hp1_ne
      have hn_ne : (q.natValue : ℝ) ≠ 0 := ne_of_gt hnat_pos
      have hn3_ne : ((q.natValue : ℝ) ^ 3) ≠ 0 := by
        exact pow_ne_zero 3 hn_ne
      have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
      have htwo_pow_ne : (2 : ℝ)^q.m ≠ 0 := by
        exact pow_ne_zero q.m htwo_ne

      have hgeom :
          ((1 / 2 : ℝ) ^ q.m) = ((2 : ℝ) ^ q.m)⁻¹ := by
        simp [one_div, inv_pow]

      rw [hgeom]
      field_simp [hp1_ne, hp1_sq_ne, hn_ne, hn3_ne, htwo_ne, htwo_pow_ne]
      have hnum_nat :
          (q.p : ℝ) * ((q.p : ℝ) + 1)^2 * (2 : ℝ)^q.m
            ≤ (q.natValue : ℝ)^3 * 8 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hnum

      have hnum_realexp :
          (q.p : ℝ) * ((q.p : ℝ) + 1) ^ (2 : ℝ) * (2 : ℝ)^q.m
            ≤ (q.natValue : ℝ)^3 * 8 := by
        simpa [Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc] using hnum_nat

      exact hnum_realexp

    exact le_trans hmajor_part htarget

  · rw [heatKernelNatValueMajorant_eq_zero_of_not_isPrimePowerPair q hq]
    have hnonneg : 0 ≤ 8 * heatKernelPairGeomModel q := by
      unfold heatKernelPairGeomModel
      positivity
    linarith

end RHFormalization
