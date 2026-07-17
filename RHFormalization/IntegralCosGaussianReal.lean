import RHFormalization.CosBumpPhaseSplit
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real Complex MeasureTheory
open scoped Real BigOperators

theorem integral_cos_mul_gaussian_real (a b : ℝ) (hb : 0 < b) :
    (∫ u : ℝ, Real.cos (a * u) * Real.exp (-b * u ^ 2))
      = Real.sqrt (Real.pi / b) * Real.exp (-a ^ 2 / (4 * b)) := by
  have hbc : (0 : ℝ) < ((b : ℂ)).re := by simpa using hb
  have hF := fourierIntegral_gaussian (b := (b : ℂ)) hbc (t := (a : ℂ))
  have hpt : ∀ x : ℝ,
      Real.cos (a * x) * Real.exp (-b * x ^ 2)
        = (Complex.exp (Complex.I * (a : ℂ) * (x : ℂ))
            * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)).re := by
    intro x
    rw [← Complex.exp_add]
    rw [show (Complex.I * (a : ℂ) * (x : ℂ) + -(b : ℂ) * (x : ℂ) ^ 2)
          = (((a * x : ℝ)) : ℂ) * Complex.I + (((-b * x ^ 2 : ℝ)) : ℂ) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    ring
  have hInt : Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * (a : ℂ) * (x : ℂ)) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)) := by
    have hg : Integrable (fun x : ℝ => Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)) :=
      integrable_cexp_neg_mul_sq hbc
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp (Complex.I * (a : ℂ) * (x : ℂ))) volume :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have hbound : ∀ᵐ x : ℝ, ‖Complex.exp (Complex.I * (a : ℂ) * (x : ℂ))‖ ≤ 1 := by
      filter_upwards with x
      rw [Complex.norm_exp]
      have hre0 : (Complex.I * (a : ℂ) * (x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hre0]; simp
    have hmul := hg.bdd_mul (c := 1) hmeas hbound
    exact hmul.congr (by filter_upwards with x; ring)
  have hstep1 : (∫ u : ℝ, Real.cos (a * u) * Real.exp (-b * u ^ 2))
      = (∫ u : ℝ, Complex.exp (Complex.I * (a : ℂ) * (u : ℂ))
            * Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2)).re := by
    have hcongr : (∫ u : ℝ, Real.cos (a * u) * Real.exp (-b * u ^ 2))
        = ∫ u : ℝ, RCLike.re (Complex.exp (Complex.I * (a : ℂ) * (u : ℂ))
            * Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [hcongr, integral_re hInt]
    rfl
  have hRHS_re : (((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(a : ℂ) ^ 2 / (4 * (b : ℂ)))).re
      = Real.sqrt (Real.pi / b) * Real.exp (-a ^ 2 / (4 * b)) := by
    have h1 : ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / b) : ℝ) : ℂ) := by
      have hnn : (0 : ℝ) ≤ Real.pi / b := by positivity
      rw [show ((Real.pi : ℂ) / (b : ℂ)) = (((Real.pi / b : ℝ)) : ℂ) by push_cast; ring]
      rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_cpow hnn]
      rw [Real.sqrt_eq_rpow]
    have h2 : Complex.exp (-(a : ℂ) ^ 2 / (4 * (b : ℂ)))
        = ((Real.exp (-a ^ 2 / (4 * b)) : ℝ) : ℂ) := by
      rw [show (-(a : ℂ) ^ 2 / (4 * (b : ℂ))) = (((-a ^ 2 / (4 * b) : ℝ)) : ℂ) by push_cast; ring,
          Complex.ofReal_exp]
    rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hstep1, hF, hRHS_re]

#print axioms integral_cos_mul_gaussian_real

end RHFormalization
