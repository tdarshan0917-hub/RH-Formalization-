import RHFormalization.PolylogMainTermIncrement
import Mathlib

/-!
# PolylogMainTermShift — PL-4b-ii-2: per-term shift bound for the main term

For `k ≥ 1`, `0 ≤ σ ≤ Re ρ`, `δ ≥ 0`:
`‖mainIncr(1−ρ) k · (k+1)^{−δ} − mainIncr(1−ρ−δ) k‖ ≤ k^{−σ}·(k^{−δ} − (k+1)^{−δ})`.
Both increments are integrals over `[k, k+1]` (PL-4b-ii-1); the integrand difference is
`x^{−ρ}·((k+1)^{−δ} − x^{−δ})`, bounded pointwise.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Pointwise bound on the shifted integrand. -/
theorem shift_integrand_norm_le {ρ : ℂ} {σ δ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ.re) (hδ : 0 ≤ δ)
    {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ (k:ℝ) + 1) :
    ‖(x:ℂ) ^ (-ρ) * (((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) - (((x ^ (-δ)) : ℝ) : ℂ))‖
      ≤ (k:ℝ) ^ (-σ) * ((k:ℝ) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ)) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have hre : (-ρ).re = -ρ.re := by simp
  rw [hre]
  have h1 : x ^ (-ρ.re) ≤ (k:ℝ) ^ (-σ) := by
    calc x ^ (-ρ.re) ≤ x ^ (-σ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (k:ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hkpos hx1 (by linarith)
  have hwx : ((k:ℝ) + 1) ^ (-δ) ≤ x ^ (-δ) := Real.rpow_le_rpow_of_nonpos hxpos hx2 (by linarith)
  have hxk : x ^ (-δ) ≤ (k:ℝ) ^ (-δ) := Real.rpow_le_rpow_of_nonpos hkpos hx1 (by linarith)
  have h2 : |((k:ℝ) + 1) ^ (-δ) - x ^ (-δ)| ≤ (k:ℝ) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ) := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  exact mul_le_mul h1 h2 (abs_nonneg _) (Real.rpow_nonneg hkpos.le _)

/-- **PL-4b-ii-2**: per-term shift bound for the main-term increments. -/
theorem mainIncr_shift_norm_le {ρ : ℂ} {σ δ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ.re) (hδ : 0 ≤ δ)
    (hρ : ρ ≠ 1) (hρδ : ρ + (δ:ℂ) ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖mainIncr (1 - ρ) k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) - mainIncr (1 - (ρ + (δ:ℂ))) k‖
      ≤ (k:ℝ) ^ (-σ) * ((k:ℝ) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ)) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hnot0 : (0:ℝ) ∉ Set.uIcc (k:ℝ) ((k:ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hI1 : IntervalIntegrable (fun x : ℝ => (x:ℂ) ^ (-ρ)) MeasureTheory.volume
      (k:ℝ) ((k:ℝ) + 1) := intervalIntegral.intervalIntegrable_cpow (Or.inr hnot0)
  have hI2 : IntervalIntegrable (fun x : ℝ => (x:ℂ) ^ (-(ρ + (δ:ℂ)))) MeasureTheory.volume
      (k:ℝ) ((k:ℝ) + 1) := intervalIntegral.intervalIntegrable_cpow (Or.inr hnot0)
  rw [mainIncr_eq_integral hρ hk, mainIncr_eq_integral hρδ hk,
    ← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_sub (hI1.mul_const _) hI2]
  have hpt : ∀ x ∈ Set.uIoc (k:ℝ) ((k:ℝ) + 1),
      ‖(x:ℂ) ^ (-ρ) * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) - (x:ℂ) ^ (-(ρ + (δ:ℂ)))‖
        ≤ (k:ℝ) ^ (-σ) * ((k:ℝ) ^ (-δ) - ((k:ℝ) + 1) ^ (-δ)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    have hsplit : (x:ℂ) ^ (-(ρ + (δ:ℂ))) = (x:ℂ) ^ (-ρ) * (((x ^ (-δ)) : ℝ) : ℂ) := by
      rw [show -(ρ + (δ:ℂ)) = -ρ + ((-δ : ℝ) : ℂ) by push_cast; ring,
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hxpos.ne'),
        ← Complex.ofReal_cpow hxpos.le]
    rw [hsplit, ← mul_sub]
    exact shift_integrand_norm_le hσ hσρ hδ hk hx.1.le hx.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show (k:ℝ) + 1 - (k:ℝ) = 1 by ring, abs_one, mul_one] at h
  exact h

#print axioms shift_integrand_norm_le
#print axioms mainIncr_shift_norm_le

end

end RHFormalization
