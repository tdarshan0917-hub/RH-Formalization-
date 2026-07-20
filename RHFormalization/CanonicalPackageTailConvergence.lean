import RHFormalization.DMRSectorTimeSplit
import RHFormalization.SlowCutoffBConvergence
import RHFormalization.BSideHeatKernelLaplaceEnvelope
import RHFormalization.ShiftedLaplacePrimeSummable
import RHFormalization.ShiftedLaplaceMajorant

/-!
# CanonicalPackageTailConvergence — T1: Gaussian-retaining short-part bounds

ROUTE CARD
1. Target: ‖kernelShortPart a t0 s‖ ≤ exp(−a²/(4t0))·C_env(s,t0), and
   summability of the weighted short family on RHP(1) by cashing the
   Gaussian against the banked kernel-norm family at the anchor s = 2.
2. The Gaussian factor is THE summability mechanism (weights alone are
   NOT summable); it was wrongly discarded in the first attempt.
3. Consumer: tail convergence (T2) = full (banked) − short (this file).
4. Raw B on Ω? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators Classical

/-- Gaussian-retaining integrand bound on (0, t0]. -/
theorem shiftedHeatIntegrand_norm_le_gaussian
    (a : ℝ) (s : ℂ) (t t0 : ℝ) (ht : 0 < t) (htt0 : t ≤ t0) :
    ‖shiftedHeatIntegrand a s t‖
      ≤ Real.exp (-(a ^ 2) / (4 * t0)) * bEnvelope (s.re + 1/4) t := by
  have hbase := shiftedHeatIntegrand_norm_le_bEnvelope a s t ht
  -- redo the sharp step: the discarded factor is exp(−a²/4t) ≤ exp(−a²/4t0)
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
  have hgauss : Real.exp (-(a ^ 2) / (4 * t)) ≤ Real.exp (-(a ^ 2) / (4 * t0)) := by
    apply Real.exp_le_exp.mpr
    have ht0' : 0 < t0 := lt_of_lt_of_le ht htt0
    have hkey : (a ^ 2) / (4 * t0) ≤ (a ^ 2) / (4 * t) := by
      gcongr
      all_goals
        first
          | exact sq_nonneg a
          | linarith
          | positivity
    have hrw1 : -(a ^ 2) / (4 * t) = -((a ^ 2) / (4 * t)) := by ring
    have hrw2 : -(a ^ 2) / (4 * t0) = -((a ^ 2) / (4 * t0)) := by ring
    rw [hrw1, hrw2]
    exact neg_le_neg hkey
  calc Real.exp (-(s.re * t)) * Real.exp (-(t/4)) *
        (1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t)))
      = Real.exp (-(a ^ 2) / (4 * t)) *
          (Real.exp (-(s.re * t)) * Real.exp (-(t/4)) *
            (1 / Real.sqrt (4 * Real.pi * t))) := by ring
    _ ≤ Real.exp (-(a ^ 2) / (4 * t0)) *
          (Real.exp (-(s.re * t)) * Real.exp (-(t/4)) *
            (1 / Real.sqrt (4 * Real.pi * t))) := by
        apply mul_le_mul_of_nonneg_right hgauss
        positivity
    _ = Real.exp (-(a ^ 2) / (4 * t0)) *
          (1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-((s.re + 1/4) * t))) := by
        rw [← hcomb]; ring

/-- Short-part norm bound with the Gaussian retained. -/
theorem kernelShortPart_norm_le_gaussian
    (a t0 : ℝ) (ht0 : 0 < t0) (s : ℂ) (hs : 0 < s.re) :
    ‖kernelShortPart a t0 s‖
      ≤ Real.exp (-(a ^ 2) / (4 * t0)) *
          ∫ t in Ioc (0:ℝ) t0, bEnvelope (s.re + 1/4) t := by
  unfold kernelShortPart
  have hc : (0:ℝ) < s.re + 1/4 := by linarith
  have hint : IntegrableOn (fun t => bEnvelope (s.re + 1/4) t) (Ioc (0:ℝ) t0) volume :=
    (bEnvelope_integrable (s.re + 1/4) hc).mono_set Ioc_subset_Ioi_self
  have hint2 : IntegrableOn
      (fun t => Real.exp (-(a ^ 2) / (4 * t0)) * bEnvelope (s.re + 1/4) t)
      (Ioc (0:ℝ) t0) volume := hint.const_mul _
  have hb : ‖∫ t in Ioc (0:ℝ) t0, shiftedHeatIntegrand a s t‖
      ≤ ∫ t in Ioc (0:ℝ) t0,
          Real.exp (-(a ^ 2) / (4 * t0)) * bEnvelope (s.re + 1/4) t := by
    refine norm_integral_le_of_norm_le hint2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact shiftedHeatIntegrand_norm_le_gaussian a s t t0 ht.1 ht.2
  refine le_trans hb (le_of_eq ?_)
  first
    | exact MeasureTheory.integral_const_mul _ _
    | exact MeasureTheory.integral_mul_left _ _
    | simp [MeasureTheory.integral_const_mul]

/-- Gaussian dominated by a tilted exponential: for a ≥ 0, σ ≥ 0,
`exp(−a²/(4t0)) ≤ exp(t0·σ²)·exp(−a·σ)`. -/
theorem gaussian_le_tilted_exp (a t0 σ : ℝ) (ht0 : 0 < t0) :
    Real.exp (-(a ^ 2) / (4 * t0))
      ≤ Real.exp (t0 * σ ^ 2) * Real.exp (-(a * σ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h4 : (0:ℝ) < 4 * t0 := by positivity
  first
    | rw [div_le_iff₀ h4]
    | rw [div_le_iff h4]
    | rw [div_le_iff_of_pos h4]
  nlinarith [sq_nonneg (a - 2 * t0 * σ), ht0, sq_nonneg a, sq_nonneg σ]

#print axioms shiftedHeatIntegrand_norm_le_gaussian
#print axioms kernelShortPart_norm_le_gaussian
#print axioms gaussian_le_tilted_exp

end

end RHFormalization
