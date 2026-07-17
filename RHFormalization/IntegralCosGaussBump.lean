import RHFormalization.IntegralSinGaussianReal
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory
open scoped Real BigOperators

/-!
# O3 brick 5a — full-line cosine transform of the normalized Gaussian bump.
∫_ℝ cos(a u) · gaussBump δ u = exp(-(a²·δ²)/2), for δ>0.
The Gaussian normalization 1/√(2πδ²) exactly cancels the transform's √(π/b) with
b = 1/(2δ²), leaving a clean exponential. Built on brick 3.
-/

theorem integral_cos_mul_gaussBump (δ : ℝ) (hδ : 0 < δ) (a : ℝ) :
    (∫ u : ℝ, Real.cos (a * u) * gaussBump δ u)
      = Real.exp (-(a ^ 2 * δ ^ 2) / 2) := by
  have hδ2 : (0 : ℝ) < 2 * δ ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 / (2 * δ ^ 2) := by positivity
  -- rewrite gaussBump and pull out the constant normalization
  have hrw : (fun u : ℝ => Real.cos (a * u) * gaussBump δ u)
      = (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi * δ ^ 2))
          * (Real.cos (a * u) * Real.exp (-(1 / (2 * δ ^ 2)) * u ^ 2))) := by
    funext u
    unfold gaussBump
    rw [show (-u ^ 2 / (2 * δ ^ 2)) = (-(1 / (2 * δ ^ 2)) * u ^ 2) by ring]
    ring
  rw [hrw, integral_const_mul, integral_cos_mul_gaussian_real a (1 / (2 * δ ^ 2)) hb]
  -- now: (1/√(2πδ²)) · (√(π/(1/(2δ²))) · exp(-a²/(4·(1/(2δ²))))) = exp(-(a²δ²)/2)
  rw [show Real.pi / (1 / (2 * δ ^ 2)) = 2 * Real.pi * δ ^ 2 by
    field_simp]
  rw [show (-a ^ 2 / (4 * (1 / (2 * δ ^ 2)))) = (-(a ^ 2 * δ ^ 2) / 2) by
    have hne : (δ : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring]
  rw [← mul_assoc]
  rw [show (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) * Real.sqrt (2 * Real.pi * δ ^ 2) = 1 by
    rw [one_div, inv_mul_cancel₀]
    exact Real.sqrt_ne_zero'.mpr (by positivity)]
  rw [one_mul]

#print axioms integral_cos_mul_gaussBump

end RHFormalization
