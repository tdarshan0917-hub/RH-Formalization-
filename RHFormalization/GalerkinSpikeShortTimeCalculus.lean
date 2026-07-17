import Mathlib

/-!
# GalerkinSpikeShortTimeCalculus

Pure real-analysis primitives for the spike sector of the head bound.
No repo donors: everything here is Mathlib-only, so it can never rot.

* `sqrt_inv_mul_exp_neg_div_le` : `t^{-1/2}·e^{-c/t} ≤ c^{-1/2}`  — the fact
  that the Gaussian at a center bounded away from 0 beats the `(4πt)^{-1/2}`
  heat-kernel prefactor, uniformly for `t > 0`.
* `gaussian_center_split` : for `a ≥ log 2`, `e^{-a²/(4t)} ≤ e^{-(log 2)·a/(4t)}`
  — converts the Gaussian into `natValue^{-σ(t)}` once `a = log natValue`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real

/-- The short-time cutoff for the spike sector. -/
def spikeT0 : ℝ := Real.log 2 / 32

theorem spikeT0_pos : 0 < spikeT0 := by
  have h : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold spikeT0; positivity

/-- `√v ≤ e^v` for `v ≥ 0`. -/
theorem sqrt_le_exp (v : ℝ) (hv : 0 ≤ v) : Real.sqrt v ≤ Real.exp v := by
  have h2 : Real.sqrt v ≤ v + 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v, sq_nonneg (Real.sqrt v - 1)]
  linarith [Real.add_one_le_exp v]

/-- **Calculus sup.** `t^{-1/2}·e^{-c/t} ≤ c^{-1/2}` for `c, t > 0`. -/
theorem sqrt_inv_mul_exp_neg_div_le (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    (Real.sqrt t)⁻¹ * Real.exp (-c / t) ≤ (Real.sqrt c)⁻¹ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hv : (0:ℝ) ≤ c / t := (div_pos hc ht).le
  have hsqle : Real.sqrt c / Real.sqrt t ≤ Real.exp (c / t) := by
    have h := sqrt_le_exp (c / t) hv
    rwa [Real.sqrt_div' c ht.le] at h
  rw [inv_mul_le_iff₀ hst]
  have hne : (-c / t : ℝ) = -(c / t) := by ring
  rw [hne, Real.exp_neg]
  calc (Real.exp (c / t))⁻¹
      ≤ (Real.sqrt c / Real.sqrt t)⁻¹ := inv_anti₀ (div_pos hsc hst) hsqle
    _ = Real.sqrt t / Real.sqrt c := by rw [inv_div]
    _ = Real.sqrt t * (Real.sqrt c)⁻¹ := div_eq_mul_inv _ _

/-- **Gaussian center split.** For `a ≥ log 2` the quadratic exponent dominates
the linear one, turning `e^{-a²/(4t)}` into a power of `e^a`. -/
theorem gaussian_center_split (a t : ℝ) (ha : Real.log 2 ≤ a) (ht : 0 < t) :
    Real.exp (-(a ^ 2) / (4 * t)) ≤ Real.exp (-(Real.log 2 * a) / (4 * t)) := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4t : (0:ℝ) < 4 * t := by linarith
  apply Real.exp_le_exp.mpr
  have hnum : -(a ^ 2) ≤ -(Real.log 2 * a) := by nlinarith [ha, h2]
  first
    | gcongr
    | (rw [div_eq_mul_inv, div_eq_mul_inv]
       exact mul_le_mul_of_nonneg_right hnum (by positivity))

#print axioms spikeT0_pos
#print axioms sqrt_le_exp
#print axioms sqrt_inv_mul_exp_neg_div_le
#print axioms gaussian_center_split

end

end RHFormalization
