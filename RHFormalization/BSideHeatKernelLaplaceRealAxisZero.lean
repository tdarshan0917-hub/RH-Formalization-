import RHFormalization.BSideHeatKernelLaplace
import RHFormalization.HeatKernelLaplaceBase
import Mathlib

namespace RHFormalization
open Real MeasureTheory Set Complex
open scoped BigOperators ComplexOrder

/-- M1 base branch: real-axis B-side identity at `a = 0`. -/
theorem shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_zero
    (σ : ℝ) (hσ : 0 < σ) :
    shiftedLaplaceHeatKernelC 0 (σ : ℂ)
      =
    ∫ t in Set.Ioi (0 : ℝ),
      shiftedHeatIntegrand 0 (σ : ℂ) t := by
  have hb : 0 < σ + (1/4 : ℝ) := by positivity
  have hB := heatKernel_laplace_base_real (σ + (1/4 : ℝ)) hb
  have hsqrt :
      Complex.sqrt ((σ + (1/4 : ℝ) : ℝ) : ℂ)
        = (Real.sqrt (σ + (1/4 : ℝ)) : ℂ) := by
    have h0 : (0 : ℂ) ≤ ((σ + (1/4 : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast le_of_lt hb
    rw [Complex.sqrt_of_nonneg h0]
    simp
  unfold shiftedLaplaceHeatKernelC shiftedHeatIntegrand heatKernelG
  rw [show ((σ : ℂ) + 1 / 4) = ((σ + (1/4 : ℝ) : ℝ) : ℂ) by push_cast; ring]
  rw [hsqrt]
  rw [show cexp (-(0:ℝ) * (Real.sqrt (σ + 1/4) : ℂ)) = 1 by simp]
  rw [mul_one]
  rw [show (1 / (2 * ((Real.sqrt (σ + (1/4 : ℝ))) : ℂ)))
        = (((1 / (2 * Real.sqrt (σ + (1/4 : ℝ)))) : ℝ) : ℂ) by push_cast; ring]
  rw [← hB]
  rw [← integral_complex_ofReal]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  simp only [neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Real.exp_zero, mul_one, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [← Complex.exp_add,
      show ((-(σ:ℂ)) * (t:ℂ) + -(t:ℂ) / 4) = ((-((σ + 1/4) * t) : ℝ) : ℂ) by push_cast; ring]
  ring

#print axioms shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_zero

end RHFormalization
