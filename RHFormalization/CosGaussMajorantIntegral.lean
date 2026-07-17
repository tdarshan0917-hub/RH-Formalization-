import RHFormalization.PartitionRiemannError
import Mathlib

/-!
# Closed-form majorant integral — G3-ii-b sub-brick 4
SENTINEL: majorant-integral-v2

ROUTE CARD
1. `integral_two_t_xi_gauss_le`: ∫₀^B 2tξ·e^{−tξ²} dξ ≤ 1 — FTC exact
   (antiderivative −e^{−tξ²}), no Gaussian evaluation needed.
2. `integral_const_gauss_le`: ∫₀^B |a|·e^{−tξ²} dξ ≤ |a|·√(π/t) — monotone
   vs the full-line Gaussian (Mathlib `integral_gaussian`).
3. `integral_cosGauss_majorant_le`: the sum, ≤ 1 + |a|·√(π/t) — what the
   partition engine's right side evaluates to.
-/

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory

/-- FTC piece: `∫₀^B 2tξ·e^{−tξ²} = 1 − e^{−tB²} ≤ 1` for t > 0, B ≥ 0. -/
theorem integral_two_t_xi_gauss_le (t B : ℝ) (ht : 0 < t) (hB : 0 ≤ B) :
    (∫ ξ in (0:ℝ)..B, 2 * t * ξ * Real.exp (-(t * ξ ^ 2))) ≤ 1 := by
  have hderiv : ∀ ξ ∈ Set.uIcc (0:ℝ) B,
      HasDerivAt (fun x : ℝ => -Real.exp (-(t * x ^ 2)))
        (2 * t * ξ * Real.exp (-(t * ξ ^ 2))) ξ := by
    intro ξ _
    have hpoly : HasDerivAt (fun x : ℝ => -(t * x ^ 2)) (-(2 * t * ξ)) ξ := by
      have h := ((hasDerivAt_pow 2 ξ).const_mul t).neg
      convert h using 1
      push_cast
      ring
    have hexp := hpoly.exp
    have h := hexp.neg
    convert h using 1
    ring
  have hint : IntervalIntegrable
      (fun ξ : ℝ => 2 * t * ξ * Real.exp (-(t * ξ ^ 2))) volume 0 B := by
    apply Continuous.intervalIntegrable
    continuity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  have hzero : -Real.exp (-(t * (0:ℝ) ^ 2)) = -1 := by
    norm_num
  rw [hzero]
  have hE : 0 < Real.exp (-(t * B ^ 2)) := Real.exp_pos _
  linarith

/-- Constant piece: `∫₀^B e^{−tξ²} ≤ √(π/t)` (dominated by the full line). -/
theorem integral_gauss_Icc_le (t B : ℝ) (ht : 0 < t) (hB : 0 ≤ B) :
    (∫ ξ in (0:ℝ)..B, Real.exp (-(t * ξ ^ 2))) ≤ Real.sqrt (Real.pi / t) := by
  have hfull : (∫ ξ : ℝ, Real.exp (-t * ξ ^ 2)) = Real.sqrt (Real.pi / t) :=
    integral_gaussian t
  have hint : Integrable (fun ξ : ℝ => Real.exp (-t * ξ ^ 2)) :=
    integrable_exp_neg_mul_sq ht
  have hshape : ∀ ξ : ℝ, Real.exp (-(t * ξ ^ 2)) = Real.exp (-t * ξ ^ 2) := by
    intro ξ
    congr 1
    ring
  simp only [hshape]
  rw [intervalIntegral.integral_of_le hB]
  calc (∫ ξ in Set.Ioc (0:ℝ) B, Real.exp (-t * ξ ^ 2))
      ≤ ∫ ξ : ℝ, Real.exp (-t * ξ ^ 2) := by
        apply setIntegral_le_integral hint
        filter_upwards with ξ
        exact (Real.exp_pos _).le
    _ = Real.sqrt (Real.pi / t) := hfull

/-- **The majorant integral**: `∫₀^B (2tξ+|a|)e^{−tξ²} ≤ 1 + |a|·√(π/t)`. -/
theorem integral_cosGauss_majorant_le (t a B : ℝ) (ht : 0 < t) (hB : 0 ≤ B) :
    (∫ ξ in (0:ℝ)..B, (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)))
      ≤ 1 + |a| * Real.sqrt (Real.pi / t) := by
  have hi1 : IntervalIntegrable
      (fun ξ : ℝ => 2 * t * ξ * Real.exp (-(t * ξ ^ 2))) volume 0 B := by
    apply Continuous.intervalIntegrable; continuity
  have hi2 : IntervalIntegrable
      (fun ξ : ℝ => |a| * Real.exp (-(t * ξ ^ 2))) volume 0 B := by
    apply Continuous.intervalIntegrable; continuity
  have hsplit : (∫ ξ in (0:ℝ)..B, (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)))
      = (∫ ξ in (0:ℝ)..B, 2 * t * ξ * Real.exp (-(t * ξ ^ 2)))
        + ∫ ξ in (0:ℝ)..B, |a| * Real.exp (-(t * ξ ^ 2)) := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    apply intervalIntegral.integral_congr
    intro ξ _
    ring
  rw [hsplit]
  have h2 : (∫ ξ in (0:ℝ)..B, |a| * Real.exp (-(t * ξ ^ 2)))
      = |a| * ∫ ξ in (0:ℝ)..B, Real.exp (-(t * ξ ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul]
  have hbound2 : (∫ ξ in (0:ℝ)..B, |a| * Real.exp (-(t * ξ ^ 2)))
      ≤ |a| * Real.sqrt (Real.pi / t) := by
    rw [h2]
    apply mul_le_mul_of_nonneg_left (integral_gauss_Icc_le t B ht hB)
      (abs_nonneg a)
  linarith [integral_two_t_xi_gauss_le t B ht hB, hbound2]

#print axioms integral_two_t_xi_gauss_le
#print axioms integral_gauss_Icc_le
#print axioms integral_cosGauss_majorant_le

end RHFormalization
