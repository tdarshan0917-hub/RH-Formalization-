import RHFormalization.DTailDensityFreeBound
import Mathlib

namespace RHFormalization
open Complex
open scoped BigOperators

theorem dTail_spectral_termwise
    {n : ℕ} (t0 : ℝ) (ht0 : 0 ≤ t0) (s : ℂ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (delta M : ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, delta ≤ ‖s + (lam i : ℂ)‖)
    (hM : |s.re| ≤ M) :
    ∀ i, ‖Complex.exp (-(t0 : ℂ) * (s + (lam i : ℂ))) / (s + (lam i : ℂ))‖
        ≤ Real.exp (t0 * M) * ((1 / delta) * Real.exp (-t0 * lam i)) := by
  intro i
  rw [norm_div]
  have hre : (-(t0 : ℂ) * (s + (lam i : ℂ))).re = -t0 * (s.re + lam i) := by
    simp [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have hnum : ‖Complex.exp (-(t0 : ℂ) * (s + (lam i : ℂ)))‖
      = Real.exp (-t0 * (s.re + lam i)) := by
    rw [Complex.norm_exp, hre]
  rw [hnum]
  have hexp_split : Real.exp (-t0 * (s.re + lam i))
      = Real.exp (-t0 * s.re) * Real.exp (-t0 * lam i) := by
    rw [← Real.exp_add]; congr 1; ring
  have hRe_le : Real.exp (-t0 * s.re) ≤ Real.exp (t0 * M) := by
    apply Real.exp_le_exp.mpr
    have hle1 : -t0 * s.re ≤ t0 * |s.re| := by
      nlinarith [neg_abs_le s.re, le_abs_self s.re, mul_nonneg ht0 (abs_nonneg s.re)]
    have hle2 : t0 * |s.re| ≤ t0 * M := mul_le_mul_of_nonneg_left hM ht0
    linarith
  have hden : 1 / ‖s + (lam i : ℂ)‖ ≤ 1 / delta := one_div_le_one_div_of_le hdelta (hgap i)
  rw [hexp_split, div_eq_mul_inv, ← one_div]
  have hnn : 0 ≤ Real.exp (-t0 * lam i) := le_of_lt (Real.exp_pos _)
  calc
    Real.exp (-t0 * s.re) * Real.exp (-t0 * lam i) * (1 / ‖s + (lam i : ℂ)‖)
        ≤ Real.exp (t0 * M) * Real.exp (-t0 * lam i) * (1 / delta) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hRe_le hnn
          · exact hden
          · positivity
          · positivity
    _ = Real.exp (t0 * M) * ((1 / delta) * Real.exp (-t0 * lam i)) := by ring

#print axioms dTail_spectral_termwise

end RHFormalization
