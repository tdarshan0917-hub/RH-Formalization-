import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Brick 2, Stone 6C-iii: the singular Beta convolution bound
`∫₀ᵗ (t-u)^{-1/2} u^{-1/2} du ≤ 4` (finite, t-independent) — integrable Beta
convolution bounding the order-2 Duhamel term (manuscript heat-smoothing). Finite
bound, not exact π. Split [0,t] at t/2; each half ≤ 2.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory
open scoped BigOperators

/-- `∫₀ᵃ u^{-1/2} du = 2·a^{1/2}` for `a ≥ 0`. -/
theorem integral_rpow_neg_half (a : ℝ) (ha : 0 ≤ a) :
    ∫ u in (0:ℝ)..a, u ^ (-(1:ℝ)/2) = 2 * a ^ ((1:ℝ)/2) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num)]
  ring_nf

/-- `u ↦ u^{-1/2}` interval-integrable on `[0,a]`. -/
theorem intervalIntegrable_rpow_neg_half (a : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ (-(1:ℝ)/2)) MeasureTheory.volume 0 a :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/-- `u ↦ (t-u)^{-1/2}` interval-integrable on `[t/2, t]`. -/
theorem intervalIntegrable_sub_rpow_neg_half (t : ℝ) :
    IntervalIntegrable (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2)) MeasureTheory.volume (t/2) t := by
  have h := (intervalIntegrable_rpow_neg_half (t/2)).comp_sub_left t
  have e1 : t - 0 = t := by ring
  have e2 : t - t/2 = t/2 := by ring
  rw [e1, e2] at h
  exact h.symm

/-- `∫_{t/2}^t (t-u)^{-1/2} du = 2·(t/2)^{1/2}` for `t > 0` (reflection of the atom). -/
theorem integral_sub_rpow_neg_half (t : ℝ) (ht : 0 < t) :
    ∫ u in (t/2)..t, (t - u) ^ (-(1:ℝ)/2) = 2 * (t/2) ^ ((1:ℝ)/2) := by
  have hcs := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1:ℝ)/2)) (a := t/2) (b := t) t
  have e1 : t - t = (0:ℝ) := by ring
  have e2 : t - t/2 = t/2 := by ring
  rw [e1, e2] at hcs
  rw [hcs, integral_rpow_neg_half (t/2) (by linarith)]

/-- **First-half Beta bound**: `∫₀^{t/2} (t-u)^{-1/2} u^{-1/2} du ≤ 2` for `t > 0`. -/
theorem beta_conv_first_half (t : ℝ) (ht : 0 < t) :
    ∫ u in (0:ℝ)..(t/2), (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) ≤ 2 := by
  have hbound : ∀ u ∈ Set.Icc (0:ℝ) (t/2),
      (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) ≤ (t/2) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) := by
    intro u hu
    obtain ⟨hu0, hu2⟩ := hu
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu0 _)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hint_lhs : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume 0 (t/2) := by
    apply (intervalIntegrable_rpow_neg_half (t/2)).continuousOn_mul
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro u hu
      left
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ t/2)] at hu
      have : (0:ℝ) < t - u := by linarith [hu.2]
      exact ne_of_gt this
  have hint_rhs : IntervalIntegrable
      (fun u : ℝ => (t/2) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume 0 (t/2) :=
    (intervalIntegrable_rpow_neg_half (t/2)).const_mul _
  refine le_trans (intervalIntegral.integral_mono_on (by linarith) hint_lhs hint_rhs hbound) ?_
  rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half (t/2) (by linarith)]
  have hpos : (0:ℝ) < t/2 := by linarith
  have hcombine : (t/2) ^ (-(1:ℝ)/2) * (2 * (t/2) ^ ((1:ℝ)/2)) = 2 := by
    rw [show (2:ℝ) * (t/2) ^ ((1:ℝ)/2) = (t/2) ^ ((1:ℝ)/2) * 2 by ring]
    rw [← mul_assoc, ← Real.rpow_add hpos]; norm_num
  rw [hcombine]

/-- **Second-half Beta bound**: `∫_{t/2}^t (t-u)^{-1/2} u^{-1/2} du ≤ 2` for `t > 0`. -/
theorem beta_conv_second_half (t : ℝ) (ht : 0 < t) :
    ∫ u in (t/2)..t, (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) ≤ 2 := by
  have hbound : ∀ u ∈ Set.Icc (t/2) t,
      (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) ≤ (t - u) ^ (-(1:ℝ)/2) * (t/2) ^ (-(1:ℝ)/2) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hint_lhs : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume (t/2) t := by
    apply (intervalIntegrable_sub_rpow_neg_half t).mul_continuousOn
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro u hu
      left
      rw [Set.uIcc_of_le (by linarith : t/2 ≤ t)] at hu
      have : (0:ℝ) < u := by linarith [hu.1]
      exact ne_of_gt this
  have hint_rhs : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * (t/2) ^ (-(1:ℝ)/2)) MeasureTheory.volume (t/2) t :=
    (intervalIntegrable_sub_rpow_neg_half t).mul_const _
  refine le_trans (intervalIntegral.integral_mono_on (by linarith) hint_lhs hint_rhs hbound) ?_
  rw [intervalIntegral.integral_mul_const, integral_sub_rpow_neg_half t ht]
  have hpos : (0:ℝ) < t/2 := by linarith
  have hcombine : 2 * (t/2) ^ ((1:ℝ)/2) * (t/2) ^ (-(1:ℝ)/2) = 2 := by
    rw [mul_assoc, ← Real.rpow_add hpos]; norm_num
  rw [hcombine]

/-- The Beta integrand `(t-u)^{-1/2} u^{-1/2}` is interval-integrable on `[0,t]`. -/
theorem intervalIntegrable_beta_integrand (t : ℝ) (ht : 0 < t) :
    IntervalIntegrable (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2))
      MeasureTheory.volume 0 t := by
  have hint1 : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume 0 (t/2) := by
    apply (intervalIntegrable_rpow_neg_half (t/2)).continuousOn_mul
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro u hu
      left
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ t/2)] at hu
      have : (0:ℝ) < t - u := by linarith [hu.2]
      exact ne_of_gt this
  have hint2 : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume (t/2) t := by
    apply (intervalIntegrable_sub_rpow_neg_half t).mul_continuousOn
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro u hu
      left
      rw [Set.uIcc_of_le (by linarith : t/2 ≤ t)] at hu
      have : (0:ℝ) < u := by linarith [hu.1]
      exact ne_of_gt this
  exact hint1.trans hint2

/-- **Full Beta convolution bound**: `∫₀ᵗ (t-u)^{-1/2} u^{-1/2} du ≤ 4` for `t > 0`. -/
theorem beta_conv_bound (t : ℝ) (ht : 0 < t) :
    ∫ u in (0:ℝ)..t, (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) ≤ 4 := by
  have hint1 : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume 0 (t/2) := by
    apply (intervalIntegrable_rpow_neg_half (t/2)).continuousOn_mul
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro u hu
      left
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ t/2)] at hu
      have : (0:ℝ) < t - u := by linarith [hu.2]
      exact ne_of_gt this
  have hint2 : IntervalIntegrable
      (fun u : ℝ => (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) MeasureTheory.volume (t/2) t := by
    apply (intervalIntegrable_sub_rpow_neg_half t).mul_continuousOn
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro u hu
      left
      rw [Set.uIcc_of_le (by linarith : t/2 ≤ t)] at hu
      have : (0:ℝ) < u := by linarith [hu.1]
      exact ne_of_gt this
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h1 := beta_conv_first_half t ht
  have h2 := beta_conv_second_half t ht
  linarith

#print axioms beta_conv_bound
end
end RHFormalization
