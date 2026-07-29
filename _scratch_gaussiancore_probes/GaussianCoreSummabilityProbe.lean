import RHFormalization.CanonicalPrimePowerHeatKernelPrimePowerSupport
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianMajorant
import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

open Filter
open scoped BigOperators

lemma nat_le_two_pow_probe (m : ℕ) :
    m ≤ 2 ^ m := by
  induction m with
  | zero =>
      norm_num
  | succ k ih =>
      have h1 : k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
      have hpos : 0 < 2 ^ k := by
        exact Nat.pow_pos (by norm_num : 0 < 2)
      have hone : 1 ≤ 2 ^ k := Nat.succ_le_of_lt hpos
      have h2 : 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := by
        exact Nat.add_le_add_left hone (2 ^ k)
      calc
        k + 1 ≤ 2 ^ k + 1 := h1
        _ ≤ 2 ^ k + 2 ^ k := h2
        _ = 2 ^ (k + 1) := by
          rw [pow_succ]
          ring

lemma valid_primePower_natValue_lt_finite_probe (N : ℕ) :
    {q : PrimePowerPair | IsPrimePowerPair q ∧ q.natValue < N}.Finite := by
  refine
    Set.Finite.subset
      (Finset.finite_toSet ((Finset.range N).product (Finset.range N)))
      ?_
  rintro ⟨p, m⟩ hq
  simp [PrimePowerPair.p, PrimePowerPair.m,
        PrimePowerPair.natValue, IsPrimePowerPair] at hq ⊢
  rcases hq with ⟨⟨hp, hm⟩, hpm_lt⟩

  have hp2 : 2 ≤ p := hp.two_le
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp2

  have hp_le_pm : p ≤ p ^ m := by
    have h1 : p ^ 1 ≤ p ^ m := by
      exact Nat.pow_le_pow_right hp_pos (Nat.succ_le_of_lt hm)
    simpa using h1

  have hp_lt_N : p < N := lt_of_le_of_lt hp_le_pm hpm_lt

  have hm_le_pm : m ≤ p ^ m := by
    have hm_le_two : m ≤ 2 ^ m := nat_le_two_pow_probe m
    have htwo_le : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp2 m
    exact le_trans hm_le_two htwo_le

  have hm_lt_N : m < N := lt_of_le_of_lt hm_le_pm hpm_lt

  exact ⟨hp_lt_N, hm_lt_N⟩

lemma eventually_not_valid_or_natValue_ge_probe (N : ℕ) :
    ∀ᶠ q : PrimePowerPair in Filter.cofinite,
      ¬ IsPrimePowerPair q ∨ N ≤ q.natValue := by
  rw [Filter.eventually_cofinite]
  refine (valid_primePower_natValue_lt_finite_probe N).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  simpa [not_or, not_le] using hq

theorem heatKernelGaussianCoreEnvelope_summable_probe
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelGaussianCoreEnvelope t) := by
  rcases heatKernelGaussianCoreEnvelope_le_weight_mul_natValue_inv_cube_of_ge t ht
    with ⟨N, hN⟩

  refine
    Summable.of_norm_bounded_eventually
      heatKernelNatValueMajorant_summable
      ?_

  filter_upwards [eventually_not_valid_or_natValue_ge_probe N] with q hq

  have hcore_nonneg : 0 ≤ heatKernelGaussianCoreEnvelope t q :=
    heatKernelGaussianCoreEnvelope_nonneg t q

  have hnorm :
      ‖heatKernelGaussianCoreEnvelope t q‖ =
        heatKernelGaussianCoreEnvelope t q := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hcore_nonneg]

  rcases hq with hbad | hlarge
  · have hz :
        heatKernelGaussianCoreEnvelope t q = 0 :=
      heatKernelGaussianCoreEnvelope_eq_zero_of_not_isPrimePowerPair t q hbad
    rw [hnorm, hz]
    unfold heatKernelNatValueMajorant
    positivity
  · rw [hnorm]
    simpa [heatKernelNatValueMajorant] using hN q hlarge

end RHFormalization
