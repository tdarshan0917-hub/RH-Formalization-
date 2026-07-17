import RHFormalization.BSideHeatKernelLaplace
import Mathlib

namespace RHFormalization
open Real MeasureTheory Set

/-- The real dominating envelope for the shifted heat integrand: `(4πt)^(-1/2)·e^{-ct}`. -/
noncomputable def bEnvelope (c t : ℝ) : ℝ :=
  (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(c * t))

/-- The envelope is integrable on `(0,∞)` for `c > 0`, via scaling the `Γ(1/2)` integral. -/
lemma bEnvelope_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (bEnvelope c) (Ioi 0) volume := by
  have hgamma : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1:ℝ)/2 - 1)) (Ioi 0) volume :=
    Real.GammaIntegral_convergent (by norm_num)
  have hscale : IntegrableOn
      (fun t : ℝ => Real.exp (-(c * t)) * (c * t) ^ ((1:ℝ)/2 - 1)) (Ioi 0) volume := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((1:ℝ)/2 - 1)) (0:ℝ) hc).mpr
    simp only [mul_zero] at h
    simpa [neg_mul] using h hgamma
  have hscale2 : IntegrableOn
      (fun t : ℝ => (Real.sqrt c / (2 * Real.sqrt Real.pi)) *
        (Real.exp (-(c * t)) * (c * t) ^ ((1:ℝ)/2 - 1))) (Ioi 0) volume :=
    hscale.const_mul (Real.sqrt c / (2 * Real.sqrt Real.pi))
  refine MeasureTheory.IntegrableOn.congr_fun hscale2 ?_ measurableSet_Ioi
  intro t ht
  simp only []
  have ht0 : 0 < t := ht
  have hsqrt4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4:ℝ) * Real.pi * t = (2 * Real.sqrt Real.pi)^2 * t by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsc : Real.sqrt c ≠ 0 := by positivity
  have hst : Real.sqrt t ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hrpow : (c * t) ^ ((1:ℝ)/2 - 1) = 1 / (Real.sqrt c * Real.sqrt t) := by
    rw [show ((1:ℝ)/2 - 1) = -(1/2:ℝ) by norm_num]
    rw [Real.rpow_neg (by positivity)]
    rw [Real.mul_rpow hc.le ht0.le]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, one_div]
  unfold bEnvelope
  rw [hrpow, hsqrt4]
  field_simp
  try ring

#print axioms bEnvelope_integrable

lemma shiftedHeatIntegrand_norm_le_bEnvelope (a : ℝ) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖shiftedHeatIntegrand a s t‖ ≤ bEnvelope (s.re + 1/4) t := by
  unfold shiftedHeatIntegrand heatKernelG bEnvelope
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs]
  have hre1 : (-s * (t:ℂ)).re = -(s.re * t) := by simp [Complex.mul_re]
  have hre2 : (-(t:ℂ)/4).re = -(t/4) := by simp ; ring
  rw [hre1, hre2]
  have hnn : (0:ℝ) ≤ 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t)) := by
    positivity
  rw [abs_of_nonneg hnn]
  have hcomb : Real.exp (-(s.re * t)) * Real.exp (-(t/4))
      = Real.exp (-((s.re + 1/4) * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_le : Real.exp (-(a ^ 2) / (4 * t)) ≤ 1 := by
    rw [show -(a ^ 2) / (4 * t) = -(a ^ 2 / (4 * t)) by ring]
    apply Real.exp_le_one_iff.mpr
    simp only [neg_nonpos]
    positivity
  calc Real.exp (-(s.re * t)) * Real.exp (-(t/4)) *
        (1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t)))
      = 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-((s.re + 1/4) * t)) *
          Real.exp (-(a ^ 2) / (4 * t)) := by rw [← hcomb]; ring
    _ ≤ 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-((s.re + 1/4) * t)) * 1 := by
        gcongr
    _ = 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-((s.re + 1/4) * t)) := by ring

#print axioms shiftedHeatIntegrand_norm_le_bEnvelope

/-- Pointwise `s`-derivative of the shifted heat integrand: `∂/∂s = -t · integrand`. -/
lemma shiftedHeatIntegrand_hasDerivAt (a t : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => shiftedHeatIntegrand a z t)
      (-(t:ℂ) * shiftedHeatIntegrand a s t) s := by
  have hfun : (fun z : ℂ => shiftedHeatIntegrand a z t)
      = fun z : ℂ => Complex.exp (-z * (t:ℂ)) * (Complex.exp (-(t:ℂ)/4) * (heatKernelG t a : ℂ)) := by
    funext z
    unfold shiftedHeatIntegrand
    ring
  rw [hfun]
  have hlin : HasDerivAt (fun z : ℂ => -z * (t:ℂ)) (-(t:ℂ)) s := by
    simpa using ((hasDerivAt_id s).neg.mul_const (t:ℂ))
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-z * (t:ℂ)))
      (-(t:ℂ) * Complex.exp (-s * (t:ℂ))) s := by
    simpa [mul_comm] using hlin.cexp
  have h2 := hexp.mul_const (Complex.exp (-(t:ℂ)/4) * (heatKernelG t a : ℂ))
  convert h2 using 1
  unfold shiftedHeatIntegrand
  ring

#print axioms shiftedHeatIntegrand_hasDerivAt

/-- Derivative-bound envelope: `t · bEnvelope c t = (4π)^{-1/2} t^{1/2} e^{-ct}`. -/
noncomputable def dEnvelope (c t : ℝ) : ℝ :=
  t * ((1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(c * t)))

lemma dEnvelope_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (dEnvelope c) (Ioi 0) volume := by
  have hgamma : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((3:ℝ)/2 - 1)) (Ioi 0) volume :=
    Real.GammaIntegral_convergent (by norm_num)
  have hscale : IntegrableOn
      (fun t : ℝ => Real.exp (-(c * t)) * (c * t) ^ ((3:ℝ)/2 - 1)) (Ioi 0) volume := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((3:ℝ)/2 - 1)) (0:ℝ) hc).mpr
    simp only [mul_zero] at h
    simpa [neg_mul] using h hgamma
  have hscale2 : IntegrableOn
      (fun t : ℝ => (1 / (2 * Real.sqrt Real.pi * Real.sqrt c)) *
        (Real.exp (-(c * t)) * (c * t) ^ ((3:ℝ)/2 - 1))) (Ioi 0) volume :=
    hscale.const_mul (1 / (2 * Real.sqrt Real.pi * Real.sqrt c))
  refine MeasureTheory.IntegrableOn.congr_fun hscale2 ?_ measurableSet_Ioi
  intro t ht
  simp only []
  have ht0 : 0 < t := ht
  have hsqrt4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4:ℝ) * Real.pi * t = (2 * Real.sqrt Real.pi)^2 * t by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsc : Real.sqrt c ≠ 0 := by positivity
  have hst : Real.sqrt t ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hrpow : (c * t) ^ ((3:ℝ)/2 - 1) = Real.sqrt c * Real.sqrt t := by
    rw [show ((3:ℝ)/2 - 1) = (1/2:ℝ) by norm_num]
    rw [Real.mul_rpow hc.le ht0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  unfold dEnvelope
  rw [hrpow, hsqrt4]
  have hsqtt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  field_simp
  nlinarith [hsqtt, Real.sqrt_nonneg t, Real.sqrt_nonneg Real.pi, Real.sqrt_nonneg c]

#print axioms dEnvelope_integrable

end RHFormalization
