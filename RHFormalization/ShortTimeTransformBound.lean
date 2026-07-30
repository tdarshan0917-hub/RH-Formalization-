-- SENTINEL: short-time-transform-bound-v2
import Mathlib

/-!
# T1a: generic short-time Laplace transform bound
`‖∫₀^{t₀} e^{−st}·f(t) dt‖ ≤ e^{M·t₀}·(2/5)·t₀^{5/2}·C` for real f with
`|f t| ≤ t^{3/2}·C` on [0,t₀] and `|s.re| ≤ M`. Self-contained.
Consumer (T1c): f := quadMass, C := SupVConst²/√π; note
`t·√t = t^{3/2}` is supplied by `rpow_three_halves_eq` below.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory intervalIntegral

/-- Bridge: `t^{3/2} = t·√t` for `0 ≤ t`. -/
theorem rpow_three_halves_eq (t : ℝ) (ht : 0 ≤ t) :
    t ^ ((3:ℝ)/2) = t * Real.sqrt t := by
  rw [show ((3:ℝ)/2) = 1 + (1/2 : ℝ) from by norm_num]
  rw [Real.rpow_add' ht (by norm_num)]
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- `∫₀^{t₀} t^{3/2} dt = (2/5)·t₀^{5/2}`. -/
theorem integral_rpow_three_halves (t0 : ℝ) :
    ∫ t in (0:ℝ)..t0, t ^ ((3:ℝ)/2) = (2/5) * t0 ^ ((5:ℝ)/2) := by
  have hr : (-1 : ℝ) < (3:ℝ)/2 := by norm_num
  rw [integral_rpow (Or.inl hr)]
  have hzero : (0:ℝ) ^ (((3:ℝ)/2) + 1) = 0 := by
    rw [show (((3:ℝ)/2) + 1) = ((5:ℝ)/2) from by norm_num]
    exact Real.zero_rpow (by norm_num)
  rw [hzero]
  rw [show (((3:ℝ)/2) + 1) = ((5:ℝ)/2) from by norm_num]
  ring

/-- **T1a: the generic short-time transform bound.** -/
theorem shortTime_transform_le
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (t0 C M : ℝ) (ht0 : 0 ≤ t0) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc (0:ℝ) t0, |f t| ≤ t ^ ((3:ℝ)/2) * C)
    (s : ℂ) (hM : |s.re| ≤ M) :
    ‖∫ t in (0:ℝ)..t0, Complex.exp (-(s * t)) * (f t : ℂ)‖
      ≤ Real.exp (M * t0) * ((2/5) * t0 ^ ((5:ℝ)/2) * C) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) hM
  have hker : ∀ t ∈ Set.Icc (0:ℝ) t0,
      ‖Complex.exp (-(s * t))‖ ≤ Real.exp (M * t0) := by
    intro t htmem
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-(s * (t:ℂ))).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [hre]
    have h1 : -(s.re * t) ≤ |s.re| * t := by
      have := neg_abs_le (s.re * t)
      have habs : |s.re * t| = |s.re| * t := by
        rw [abs_mul, abs_of_nonneg htmem.1]
      nlinarith [abs_nonneg (s.re * t), neg_abs_le (s.re * t)]
    calc -(s.re * t) ≤ |s.re| * t := h1
      _ ≤ M * t0 := by
          apply mul_le_mul hM htmem.2 htmem.1 hMnn
  have hcont_integrand : Continuous
      (fun t : ℝ => Complex.exp (-(s * t)) * (f t : ℂ)) := by
    fun_prop
  calc ‖∫ t in (0:ℝ)..t0, Complex.exp (-(s * t)) * (f t : ℂ)‖
      ≤ ∫ t in (0:ℝ)..t0, ‖Complex.exp (-(s * t)) * (f t : ℂ)‖ := by
        first
          | exact intervalIntegral.norm_integral_le_integral_norm ht0
          | (have h := intervalIntegral.norm_integral_le_integral_norm
              (f := fun t : ℝ => Complex.exp (-(s * t)) * (f t : ℂ))
              (μ := MeasureTheory.volume) ht0
             simpa using h)
    _ ≤ ∫ t in (0:ℝ)..t0, Real.exp (M * t0) * (t ^ ((3:ℝ)/2) * C) := by
        apply intervalIntegral.integral_mono_on ht0
        · exact hcont_integrand.norm.intervalIntegrable 0 t0
        · apply Continuous.intervalIntegrable
          have hrpow : Continuous (fun u : ℝ => u ^ ((3:ℝ)/2)) :=
            Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ (3:ℝ)/2)
          exact continuous_const.mul ((hrpow.mul continuous_const))
        · intro t htmem
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (hker t htmem) (hf t htmem) (abs_nonneg _)
            (le_of_lt (Real.exp_pos _))
    _ = Real.exp (M * t0) * ((2/5) * t0 ^ ((5:ℝ)/2) * C) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [show (fun t : ℝ => t ^ ((3:ℝ)/2) * C)
            = fun t : ℝ => C * t ^ ((3:ℝ)/2) from by
          funext t; ring]
        rw [intervalIntegral.integral_const_mul]
        rw [integral_rpow_three_halves]
        ring

#print axioms rpow_three_halves_eq
#print axioms integral_rpow_three_halves
#print axioms shortTime_transform_le

end

end RHFormalization
