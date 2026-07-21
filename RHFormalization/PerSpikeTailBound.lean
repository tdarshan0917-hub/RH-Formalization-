import RHFormalization.BTailExplicitForm
import RHFormalization.RateLaplaceIntegrals
import Mathlib

/-!
# PerSpikeTailBound — C2: per-spike tail integrand ≤ e^{−a/2}·envelope

ROUTE CARD
1. Target: pointwise, t > 0: ‖shiftedHeatIntegrand a s t‖ ≤
   e^{−Re(s)t}·e^{−a/2}/√(4πt), via AM–GM t/4 + a²/(4t) ≥ a/2.
   e^{−a/2} converts spike mass Λ(q)/√q into Λ(q)/q — summable.
2. Consumer: C3 (summed B-tail bound) → B-tail control → O3.
3. Raw B on Ω? NO — Re s > 0 rep integrand bound only.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set

/-- AM–GM: `a/2 ≤ t/4 + a²/(4t)` for t > 0, a ≥ 0. -/
theorem quarter_amgm (a t : ℝ) (ht : 0 < t) (ha : 0 ≤ a) :
    a / 2 ≤ t / 4 + a ^ 2 / (4 * t) := by
  have hsq : 0 ≤ (t - a) ^ 2 := sq_nonneg _
  have hdiv : a / 2 * (4 * t) ≤ (t / 4 + a ^ 2 / (4 * t)) * (4 * t) := by
    have hL : a / 2 * (4 * t) = 2 * a * t := by ring
    have hR : (t / 4 + a ^ 2 / (4 * t)) * (4 * t) = t ^ 2 + a ^ 2 := by
      field_simp
    rw [hL, hR]
    nlinarith [hsq]
  have h4t : (0:ℝ) < 4 * t := by linarith
  exact le_of_mul_le_mul_right hdiv h4t

/-- **C2: the per-spike tail integrand bound.** -/
theorem shiftedHeatIntegrand_norm_le_center_decay
    (a : ℝ) (ha : 0 ≤ a) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖shiftedHeatIntegrand a s t‖
      ≤ Real.exp (-s.re * t) * Real.exp (-(a / 2))
          * (1 / Real.sqrt (4 * Real.pi * t)) := by
  unfold shiftedHeatIntegrand heatKernelG
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  have hre1 : (-s * (t:ℂ)).re = -s.re * t := by
    simp [Complex.mul_re]
  have hre2 : (-(t:ℂ)/4).re = -(t/4) := by
    simp
    ring
  rw [hre1, hre2]
  have hG : |(1 : ℝ) / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t))|
      = (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(a ^ 2) / (4 * t)) := by
    apply abs_of_nonneg
    positivity
  rw [hG]
  have hcombine : Real.exp (-(t/4)) * Real.exp (-(a ^ 2) / (4 * t))
      ≤ Real.exp (-(a / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := quarter_amgm a t ht ha
    have hrw : -(t/4) + -(a ^ 2) / (4 * t) = -(t / 4 + a ^ 2 / (4 * t)) := by
      ring
    rw [hrw]
    linarith
  calc Real.exp (-s.re * t) * Real.exp (-(t/4))
        * ((1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(a ^ 2) / (4 * t)))
      = Real.exp (-s.re * t)
        * (Real.exp (-(t/4)) * Real.exp (-(a ^ 2) / (4 * t)))
        * (1 / Real.sqrt (4 * Real.pi * t)) := by ring
    _ ≤ Real.exp (-s.re * t) * Real.exp (-(a / 2))
        * (1 / Real.sqrt (4 * Real.pi * t)) := by
        have h1 : (0:ℝ) ≤ Real.exp (-s.re * t) := Real.exp_nonneg _
        have h2 : (0:ℝ) ≤ 1 / Real.sqrt (4 * Real.pi * t) := by positivity
        have hmid : Real.exp (-s.re * t)
            * (Real.exp (-(t/4)) * Real.exp (-(a ^ 2) / (4 * t)))
            ≤ Real.exp (-s.re * t) * Real.exp (-(a / 2)) :=
          mul_le_mul_of_nonneg_left hcombine h1
        exact mul_le_mul_of_nonneg_right hmid h2

#print axioms quarter_amgm
#print axioms shiftedHeatIntegrand_norm_le_center_decay

end

end RHFormalization
