import RHFormalization.BSideHeatKernelLaplace
import RHFormalization.GlasserIntegral
import RHFormalization.HeatKernelLaplaceBase
import Mathlib

namespace RHFormalization
open Real MeasureTheory Set Complex
open scoped BigOperators ComplexOrder

/-- Positive-shift heat-kernel Laplace identity (real form), via Glasser + t = x^2. -/
theorem heatKernel_laplace_pos_real (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    (∫ t in Ioi (0:ℝ),
        (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(b * t)) * Real.exp (-(a^2 / (4 * t))))
      = Real.exp (-(a * Real.sqrt b)) / (2 * Real.sqrt b) := by
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => (1 / Real.sqrt (4 * Real.pi * y)) * Real.exp (-(b * y)) * Real.exp (-(a^2 / (4 * y))))
    (p := 2) (by norm_num : (0:ℝ) < 2)
  rw [← hsub]
  have hint : (∫ x in Ioi (0:ℝ),
        (2 * x ^ ((2:ℝ) - 1)) •
          ((1 / Real.sqrt (4 * Real.pi * x ^ (2:ℝ))) * Real.exp (-(b * x ^ (2:ℝ))) *
            Real.exp (-(a^2 / (4 * x ^ (2:ℝ))))))
      = ∫ x in Ioi (0:ℝ),
          (1 / Real.sqrt Real.pi) * Real.exp (-(b * x^2 + (a/2)^2 / x^2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := mem_Ioi.mp hx
    simp only [smul_eq_mul]
    have hxsq : x ^ (2:ℝ) = x^2 := Real.rpow_two x
    rw [hxsq]
    have h21 : x ^ ((2:ℝ) - 1) = x := by
      rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [h21]
    have hsqrt : Real.sqrt (4 * Real.pi * x^2) = 2 * Real.sqrt Real.pi * x := by
      rw [show (4:ℝ) * Real.pi * x^2 = (2 * Real.sqrt Real.pi * x)^2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
      rw [Real.sqrt_sq (by positivity)]
    rw [hsqrt]
    have hexp : Real.exp (-(b * x ^ 2)) * Real.exp (-(a ^ 2 / (4 * x ^ 2)))
        = Real.exp (-(b * x ^ 2 + (a / 2) ^ 2 / x ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← hexp]
    field_simp
    try ring
  rw [hint, integral_const_mul,
      glasser_integral b (a/2) hb (by positivity),
      show 2 * (a/2) * Real.sqrt b = a * Real.sqrt b by ring]
  have hsp : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsb : (0:ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp
  try ring

/-- M1 positive branch: complex-cast wrapper of the positive-shift identity. -/
theorem shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_pos (a σ : ℝ) (ha_pos : 0 < a) (hσ : 0 < σ) :
    shiftedLaplaceHeatKernelC a (σ : ℂ)
      =
    ∫ t in Set.Ioi (0 : ℝ), shiftedHeatIntegrand a (σ : ℂ) t := by
  have hb : 0 < σ + (1/4 : ℝ) := by positivity
  have hD := heatKernel_laplace_pos_real (σ + (1/4 : ℝ)) a hb ha_pos
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
  rw [show cexp (-(a:ℝ) * ((Real.sqrt (σ + (1/4 : ℝ)) : ℝ) : ℂ))
        = ((Real.exp (-(a * Real.sqrt (σ + (1/4 : ℝ)))) : ℝ) : ℂ) by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
  rw [show (1 / (2 * ((Real.sqrt (σ + (1/4 : ℝ))) : ℂ)) *
        ((Real.exp (-(a * Real.sqrt (σ + (1/4 : ℝ)))) : ℝ) : ℂ))
        = (((Real.exp (-(a * Real.sqrt (σ + (1/4 : ℝ)))) / (2 * Real.sqrt (σ + (1/4 : ℝ)))) : ℝ) : ℂ) by
      push_cast; ring]
  rw [← hD]
  rw [← integral_complex_ofReal]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  rw [show ((-(a^2 / (4 * t)) : ℝ) : ℂ) = ((-a^2 / (4 * t) : ℝ) : ℂ) by norm_num [neg_div]]
  rw [show ((-((σ + (1/4:ℝ)) * t) : ℝ) : ℂ) = (-(σ:ℂ) * (t:ℂ) + -(t:ℂ) / 4) by push_cast; ring]
  rw [Complex.exp_add]
  ring

#print axioms heatKernel_laplace_pos_real
#print axioms shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_pos

end RHFormalization
