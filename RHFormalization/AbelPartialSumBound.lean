import Mathlib

/-!
# AbelPartialSumBound — RHC-2a: power-weighted partial sums from partial-sum growth

If `c 0 = 0` and `‖Σ_{k ≤ t} c k‖ ≤ C t^{1/2+ε}` for `t > 0`, then for `Re ρ > 1/2 + ε` and `Y ≥ 1`:
`‖Σ_{0<k≤Y} k^{-ρ} c k‖ ≤ C + ‖ρ‖ C (1/2)^{1/2+ε-Re ρ}/(Re ρ − 1/2 − ε)` — uniform in `Y`.
Proof: Mathlib's Abel summation on `[1/2, Y]` with `f t = t^{-ρ}`, `f' = -ρ t^{-ρ-1}`.
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

theorem hasDerivAt_ofReal_cpow_const (c : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hslit : (t : ℂ) ∈ Complex.slitPlane := by
    first
      | exact Complex.ofReal_mem_slitPlane.mpr ht
      | exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using ht))
  have h1 : HasDerivAt (fun z : ℂ => z ^ c) (c * (t : ℂ) ^ (c - 1)) (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).cpow_const (c := c) hslit
  exact h1.comp_ofReal

/-- **RHC-2a — Abel bound.** -/
theorem abel_partial_sum_bound (ρ : ℂ) (c : ℕ → ℂ) (hc0 : c 0 = 0) (C ε : ℝ) (hC : 0 ≤ C)
    (hp : 1/2 + ε < ρ.re)
    (hA : ∀ t : ℝ, 0 < t → ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C * t ^ (1/2 + ε))
    {Y : ℝ} (hY : 1 ≤ Y) :
    ‖∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, ((k : ℝ) : ℂ) ^ (-ρ) * c k‖
      ≤ C + ‖ρ‖ * C * ((1/2 : ℝ) ^ (1/2 + ε - ρ.re) / (ρ.re - 1/2 - ε)) := by
  have hYpos : 0 < Y := by linarith
  have hhalfY : (1/2 : ℝ) ≤ Y := by linarith
  have hdiff : ∀ t ∈ Set.Icc (1/2 : ℝ) Y, DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-ρ)) t :=
    fun t ht => (hasDerivAt_ofReal_cpow_const (-ρ) (by linarith [ht.1])).differentiableAt
  have hint : MeasureTheory.IntegrableOn (deriv (fun y : ℝ => (y : ℂ) ^ (-ρ)))
      (Set.Icc (1/2 : ℝ) Y) MeasureTheory.volume := by
    have hcont : ContinuousOn (fun t : ℝ => -ρ * (t : ℂ) ^ (-ρ - 1)) (Set.Icc (1/2 : ℝ) Y) :=
      fun t ht => (continuousAt_const.mul
        (hasDerivAt_ofReal_cpow_const (-ρ - 1) (by linarith [ht.1])).continuousAt).continuousWithinAt
    have heq : Set.EqOn (deriv (fun y : ℝ => (y : ℂ) ^ (-ρ)))
        (fun t : ℝ => -ρ * (t : ℂ) ^ (-ρ - 1)) (Set.Icc (1/2 : ℝ) Y) :=
      fun t ht => (hasDerivAt_ofReal_cpow_const (-ρ) (by linarith [ht.1])).deriv
    exact (hcont.congr heq).integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := fun y : ℝ => (y : ℂ) ^ (-ρ))
    (a := 1/2) (b := Y) (by norm_num) hhalfY hdiff hint
  have hfloor : ⌊(1/2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  rw [hfloor, Finset.Icc_self, Finset.sum_singleton, hc0, mul_zero, sub_zero] at habel
  try beta_reduce at habel
  rw [habel]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · -- boundary term
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos, Complex.neg_re]
    calc Y ^ (-ρ.re) * ‖∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, c k‖
        ≤ Y ^ (-ρ.re) * (C * Y ^ (1/2 + ε)) :=
          mul_le_mul_of_nonneg_left (hA Y hYpos) (by positivity)
      _ = C * Y ^ (-ρ.re + (1/2 + ε)) := by rw [Real.rpow_add hYpos (-ρ.re) (1/2 + ε)]; ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hY (by linarith)) hC
      _ = C := mul_one C
  · -- integral term
    have hnot0 : (0 : ℝ) ∉ Set.uIcc (1/2 : ℝ) Y := by
      rw [Set.uIcc_of_le hhalfY]
      intro h
      linarith [h.1]
    rw [← intervalIntegral.integral_of_le hhalfY]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le hhalfY
      (g := fun t : ℝ => ‖ρ‖ * C * t ^ (1/2 + ε - ρ.re - 1))
      (Filter.Eventually.of_forall (fun t ht => ?_)) ?_) ?_
    · have htpos : 0 < t := by linarith [ht.1]
      rw [(hasDerivAt_ofReal_cpow_const (-ρ) htpos).deriv, norm_mul, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-ρ - 1).re = -ρ.re - 1 := by simp
      rw [hre]
      calc ‖ρ‖ * t ^ (-ρ.re - 1) * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖
          ≤ ‖ρ‖ * t ^ (-ρ.re - 1) * (C * t ^ (1/2 + ε)) :=
            mul_le_mul_of_nonneg_left (hA t htpos) (by positivity)
        _ = ‖ρ‖ * C * t ^ ((-ρ.re - 1) + (1/2 + ε)) := by
            rw [Real.rpow_add htpos (-ρ.re - 1) (1/2 + ε)]; ring
        _ = ‖ρ‖ * C * t ^ (1/2 + ε - ρ.re - 1) := by ring_nf
    · first
        | exact (intervalIntegral.intervalIntegrable_rpow (Or.inr hnot0)).const_mul (‖ρ‖ * C)
        | exact ((intervalIntegral.intervalIntegrable_rpow (r := 1/2 + ε - ρ.re - 1)
            (Or.inr hnot0)).const_mul (‖ρ‖ * C))
    · rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inr ⟨fun h => by linarith, hnot0⟩)]
      rw [show (1/2 + ε - ρ.re - 1 + 1) = (1/2 + ε - ρ.re) by ring]
      have hq : 0 < ρ.re - 1/2 - ε := by linarith
      have hp0 : (1/2 + ε - ρ.re) ≠ 0 := (show 1/2 + ε - ρ.re < 0 by linarith).ne
      have hYp : 0 ≤ Y ^ (1/2 + ε - ρ.re) := Real.rpow_nonneg hYpos.le _
      have e : (Y ^ (1/2 + ε - ρ.re) - (1/2 : ℝ) ^ (1/2 + ε - ρ.re)) / (1/2 + ε - ρ.re)
          = ((1/2 : ℝ) ^ (1/2 + ε - ρ.re) - Y ^ (1/2 + ε - ρ.re)) / (ρ.re - 1/2 - ε) := by
        first
          | (rw [div_eq_div_iff hp0 hq.ne']; ring)
          | (rw [show ρ.re - 1/2 - ε = -(1/2 + ε - ρ.re) by ring, div_neg, ← neg_div, neg_sub])
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      gcongr
      linarith

#print axioms hasDerivAt_ofReal_cpow_const
#print axioms abel_partial_sum_bound

end RHFormalization
