import RHFormalization.AbelPartialSumBound
import RHFormalization.ZetaDiscrepancyBound
import Mathlib

/-!
# VonKochDiscrepancyBound — RHC-2b: von Koch bound ⇒ real-cutoff discrepancy bounded

Hypothesis (von Koch type, implied by RH): `|ψ(t) − t| ≤ C t^{1/2+δ/2}` for `t ≥ 1`.
Conclusion: on `{Re ρ ≥ 1/2+δ, ‖ρ‖ ≤ R, ρ ≠ 1}`, uniformly in real `Y ≥ 1`,
`‖Σ_{0<k≤Y} Λ(k)k^{-ρ} − (Y^{1-ρ}−1)/(1−ρ)‖ ≤ B`.
Split `Λ = (Λ−1) + 1`: Abel part (RHC-2a, partial sums `ψ(t)−⌊t⌋`), ζ part (CV-1), and the
integer/real cutoff gap `∫_{⌊Y⌋}^{Y} t^{-ρ} dt` (norm ≤ 1).
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

theorem vmDiscrepancyReal_bound (δ R C : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hVK : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1/2 + δ/2)) :
    ∃ B : ℝ, ∀ ρ : ℂ, 1/2 + δ ≤ ρ.re → ‖ρ‖ ≤ R → ρ ≠ 1 → ∀ Y : ℝ, 1 ≤ Y →
      ‖(∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊,
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ k)
        - (((Y : ℂ)) ^ (1 - ρ) - 1) / (1 - ρ)‖ ≤ B := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun k =>
      if k = 0 then 0 else ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) - 1 := ⟨_, rfl⟩
  have hc0 : c 0 = 0 := by rw [hc]; simp
  have hcsum : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, c k
      = (∑ k ∈ Finset.Icc 0 m, ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) - (m : ℂ) := by
    intro m
    induction m with
    | zero => simp [hc]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (Nat.zero_le _), Finset.sum_Icc_succ_top (Nat.zero_le _), ih]
      simp only [hc, Nat.add_one_ne_zero, ↓reduceIte]
      push_cast
      ring
  have hA : ∀ t : ℝ, 0 < t → ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ (C + 1) * t ^ (1/2 + δ/2) := by
    intro t ht
    rw [hcsum ⌊t⌋₊]
    have hψ : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        = ((Chebyshev.psi t : ℝ) : ℂ) := by
      rw [Chebyshev.psi_eq_sum_Icc, Complex.ofReal_sum]
    rw [hψ]
    have hcast : ((Chebyshev.psi t : ℝ) : ℂ) - ((⌊t⌋₊ : ℕ) : ℂ)
        = ((Chebyshev.psi t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    first
      | rw [Complex.norm_real, Real.norm_eq_abs]
      | rw [Complex.norm_ofReal]
      | rw [Complex.abs_ofReal]
    by_cases ht1 : 1 ≤ t
    · have h1 := hVK t ht1
      have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht.le
      have hfl2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h2 : |t - (⌊t⌋₊ : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h3 : (1 : ℝ) ≤ t ^ (1/2 + δ/2) := Real.one_le_rpow ht1 (by positivity)
      have htri : |Chebyshev.psi t - (⌊t⌋₊ : ℝ)|
          ≤ |Chebyshev.psi t - t| + |t - (⌊t⌋₊ : ℝ)| := by
        have := abs_sub_le (Chebyshev.psi t) t (⌊t⌋₊ : ℝ)
        exact this
      nlinarith
    · have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (not_le.mp ht1)
      have hψ0 : Chebyshev.psi t = 0 := by rw [Chebyshev.psi_eq_sum_Icc, hf]; simp
      rw [hψ0, hf]
      simp only [Nat.cast_zero, sub_zero, abs_zero]
      positivity
  obtain ⟨Bz, hBz⟩ := zetaDiscrepancy_bounded (c := 1/2) (R := R) (by norm_num)
  refine ⟨(C + 1) + R * (C + 1) * ((1/2 : ℝ) ^ (-R) / (δ/2)) + Bz + 1,
    fun ρ hρre hρR hρ1 Y hY => ?_⟩
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hρR
  have hreR : ρ.re ≤ R := le_trans (Complex.re_le_norm ρ) hρR
  have hM1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hM1r : (1 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hM1
  have hMY : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  -- decomposition Λ = (Λ − 1) + 1
  have hdecomp : (∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊,
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ k)
      = (∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, ((k : ℝ) : ℂ) ^ (-ρ) * c k)
        + ∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, (k : ℂ) ^ (-ρ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk0 : k ≠ 0 := (Finset.mem_Ioc.mp hk).1.ne'
    rw [LSeries.term_of_ne_zero hk0, hc]
    simp only [hk0, ↓reduceIte, Complex.ofReal_natCast, Complex.cpow_neg]
    ring
  -- cutoff gap
  have hE : ‖((((⌊Y⌋₊ : ℕ) : ℝ) : ℂ) ^ (1 - ρ) - (Y : ℂ) ^ (1 - ρ)) / (1 - ρ)‖ ≤ 1 := by
    have hnot0 : (0 : ℝ) ∉ Set.uIcc ((⌊Y⌋₊ : ℕ) : ℝ) Y := by
      rw [Set.uIcc_of_le hMY]
      intro h
      linarith [h.1]
    have hint := integral_cpow (a := ((⌊Y⌋₊ : ℕ) : ℝ)) (b := Y) (r := -ρ)
      (Or.inr ⟨fun h => hρ1 (neg_inj.mp h), hnot0⟩)
    rw [show (-ρ + 1) = 1 - ρ by ring] at hint
    have hEq : ((((⌊Y⌋₊ : ℕ) : ℝ) : ℂ) ^ (1 - ρ) - (Y : ℂ) ^ (1 - ρ)) / (1 - ρ)
        = -∫ x in ((⌊Y⌋₊ : ℕ) : ℝ)..Y, (x : ℂ) ^ (-ρ) := by
      rw [hint]
      ring
    rw [hEq, norm_neg]
    calc ‖∫ x in ((⌊Y⌋₊ : ℕ) : ℝ)..Y, (x : ℂ) ^ (-ρ)‖
        ≤ ∫ x in ((⌊Y⌋₊ : ℕ) : ℝ)..Y, (1 : ℝ) :=
          intervalIntegral.norm_integral_le_of_norm_le hMY
            (Filter.Eventually.of_forall (fun t ht => by
              have ht1 : (1 : ℝ) ≤ t := le_trans hM1r ht.1.le
              rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
              exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)))
            intervalIntegrable_const
      _ = Y - (⌊Y⌋₊ : ℝ) := by simp
      _ ≤ 1 := by linarith [Nat.lt_floor_add_one Y]
  -- Abel part, uniformized
  have hAbel := abel_partial_sum_bound ρ c hc0 (C + 1) (δ/2) (by linarith)
    (by linarith) hA hY
  have hx : (1/2 : ℝ) ^ (1/2 + δ/2 - ρ.re) ≤ (1/2 : ℝ) ^ (-R) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
  have hq : δ/2 ≤ ρ.re - 1/2 - δ/2 := by linarith
  have hfrac : (1/2 : ℝ) ^ (1/2 + δ/2 - ρ.re) / (ρ.re - 1/2 - δ/2)
      ≤ (1/2 : ℝ) ^ (-R) / (δ/2) := by
    have hpos1 : (0 : ℝ) < δ/2 := by linarith
    have hpos2 : (0 : ℝ) < ρ.re - 1/2 - δ/2 := by linarith
    rw [div_le_div_iff₀ hpos2 hpos1]
    have hnn : (0 : ℝ) ≤ (1/2 : ℝ) ^ (-R) := Real.rpow_nonneg (by norm_num) _
    calc (1/2 : ℝ) ^ (1/2 + δ/2 - ρ.re) * (δ/2) ≤ (1/2 : ℝ) ^ (-R) * (δ/2) :=
          mul_le_mul_of_nonneg_right hx hpos1.le
      _ ≤ (1/2 : ℝ) ^ (-R) * (ρ.re - 1/2 - δ/2) := mul_le_mul_of_nonneg_left hq hnn
  have hAbelU : ‖∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, ((k : ℝ) : ℂ) ^ (-ρ) * c k‖
      ≤ (C + 1) + R * (C + 1) * ((1/2 : ℝ) ^ (-R) / (δ/2)) := by
    refine le_trans hAbel (add_le_add le_rfl ?_)
    have hfrac0 : 0 ≤ (1/2 : ℝ) ^ (1/2 + δ/2 - ρ.re) / (ρ.re - 1/2 - δ/2) := by
      apply div_nonneg (Real.rpow_nonneg (by norm_num) _); linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hρR (by linarith)) hfrac hfrac0
      (by positivity)
  have hZ := hBz ρ (by linarith) hρR hρ1 ⌊Y⌋₊ hM1
  -- assemble
  have hsplit : (∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊,
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ k)
        - (((Y : ℂ)) ^ (1 - ρ) - 1) / (1 - ρ)
      = (∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, ((k : ℝ) : ℂ) ^ (-ρ) * c k)
        + zetaDiscrepancy ⌊Y⌋₊ ρ
        + ((((⌊Y⌋₊ : ℕ) : ℝ) : ℂ) ^ (1 - ρ) - (Y : ℂ) ^ (1 - ρ)) / (1 - ρ) := by
    rw [hdecomp]
    unfold zetaDiscrepancy
    rw [Complex.ofReal_natCast]
    ring
  rw [hsplit]
  have t1 := norm_add_le ((∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, ((k : ℝ) : ℂ) ^ (-ρ) * c k)
      + zetaDiscrepancy ⌊Y⌋₊ ρ)
    (((((⌊Y⌋₊ : ℕ) : ℝ) : ℂ) ^ (1 - ρ) - (Y : ℂ) ^ (1 - ρ)) / (1 - ρ))
  have t2 := norm_add_le (∑ k ∈ Finset.Ioc 0 ⌊Y⌋₊, ((k : ℝ) : ℂ) ^ (-ρ) * c k)
    (zetaDiscrepancy ⌊Y⌋₊ ρ)
  linarith

#print axioms vmDiscrepancyReal_bound

end RHFormalization
