-- SENTINEL: short-time-u-integral-v3
import Mathlib

/-!
# Brick (b2): the u-integration real-analysis kit
Self-contained, no matrices. `∫₀ᵗ (t−u)^(−1/2) du = 2√t`; sqrt-argument
simplification; pointwise domination of the sqrt-variant constant; the
integrated dominant. DOWNSTREAM CONSUMER: u-integration of
quadRemainder_trace_sqrt_le → short-time sector mass → h_conv.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- **(1) The reflected rpow integral:** `∫₀ᵗ (t−u)^(−1/2) du = 2√t`. -/
theorem integral_sub_rpow_neg_half (t : ℝ) :
    ∫ u in (0:ℝ)..t, (t - u) ^ (-(1/2) : ℝ) = 2 * Real.sqrt t := by
  have hrefl : ∫ u in (0:ℝ)..t, (t - u) ^ (-(1/2) : ℝ)
      = ∫ v in (0:ℝ)..t, v ^ (-(1/2) : ℝ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (0:ℝ)) (b := t) (fun v : ℝ => v ^ (-(1/2) : ℝ)) t
    simpa using h
  rw [hrefl]
  have hr : (-1 : ℝ) < -(1/2) := by norm_num
  rw [integral_rpow (Or.inl hr)]
  have hzero : (0:ℝ) ^ ((-(1/2) : ℝ) + 1) = 0 := by
    rw [show ((-(1/2) : ℝ) + 1) = (1/2 : ℝ) from by norm_num]
    exact Real.zero_rpow (by norm_num)
  rw [hzero]
  rw [show ((-(1/2) : ℝ) + 1) = (1/2 : ℝ) from by norm_num]
  rw [show Real.sqrt t = t ^ (1/2 : ℝ) from Real.sqrt_eq_rpow t]
  ring

/-- **(2) sqrt-argument simplification** at L=1. -/
theorem sqrt_pi_div_arg (x : ℝ) (hx : 0 < x) :
    Real.sqrt (Real.pi / (x * (Real.pi / 1) ^ 2))
      = 1 / (Real.sqrt Real.pi * Real.sqrt x) := by
  have harg : Real.pi / (x * (Real.pi / 1) ^ 2) = 1 / (x * Real.pi) := by
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    first
      | (field_simp; ring)
      | field_simp
  rw [harg, one_div, Real.sqrt_inv, Real.sqrt_mul (le_of_lt hx),
    mul_comm (Real.sqrt x) (Real.sqrt Real.pi)]
  exact (one_div _).symm

/-- **(3a) pointwise domination:** the sqrt-variant constant against the
rpow integrand, for `0 ≤ u < t`, `0 ≤ S`. -/
theorem sqrtConstant_le_rpow (t u S : ℝ) (hu : 0 ≤ u) (hut : u < t)
    (hS : 0 ≤ S) :
    u * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2) * S)
      ≤ (t * S / (2 * Real.sqrt Real.pi)) * (t - u) ^ (-(1/2) : ℝ) := by
  have htu : (0:ℝ) < t - u := by linarith
  have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hstu : (0:ℝ) < Real.sqrt (t - u) := Real.sqrt_pos.mpr htu
  rw [sqrt_pi_div_arg (t - u) htu]
  have hrpow : (t - u) ^ (-(1/2) : ℝ) = 1 / Real.sqrt (t - u) := by
    rw [Real.rpow_neg (le_of_lt htu), ← Real.sqrt_eq_rpow, one_div]
  rw [hrpow]
  have hLHS : u * (1 / (Real.sqrt Real.pi * Real.sqrt (t - u)) / 2 * S)
      = u * S / (2 * (Real.sqrt Real.pi * Real.sqrt (t - u))) := by
    first
      | (field_simp; ring)
      | field_simp
  have hRHS : t * S / (2 * Real.sqrt Real.pi) * (1 / Real.sqrt (t - u))
      = t * S / (2 * (Real.sqrt Real.pi * Real.sqrt (t - u))) := by
    first
      | (field_simp; ring)
      | field_simp
  rw [hLHS, hRHS]
  first
    | exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_of_lt hut) hS) (by positivity)
    | exact div_le_div_of_le_left
        (mul_le_mul_of_nonneg_right (le_of_lt hut) hS) (by positivity)
        (by positivity)
    | exact div_le_div_of_nonneg
        (mul_le_mul_of_nonneg_right (le_of_lt hut) hS) (by positivity)
    | (apply div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_of_lt hut) hS)
       positivity)
    | (apply div_le_div_of_le
       · exact by positivity
       · exact mul_le_mul_of_nonneg_right (le_of_lt hut) hS)
    | exact (div_le_div_iff_of_pos_right (by positivity)).mpr
        (mul_le_mul_of_nonneg_right (le_of_lt hut) hS)
    | (rw [div_le_div_iff (by positivity) (by positivity)]
       nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hut) hS,
         mul_pos hπ hstu])

/-- **(3b) the integrated short-time mass:** `∫₀ᵗ` of the domination RHS. -/
theorem integral_rpow_dominant (t S : ℝ) :
    ∫ u in (0:ℝ)..t, (t * S / (2 * Real.sqrt Real.pi))
        * (t - u) ^ (-(1/2) : ℝ)
      = t * Real.sqrt t * S / Real.sqrt Real.pi := by
  rw [intervalIntegral.integral_const_mul]
  rw [integral_sub_rpow_neg_half t]
  have hπ : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  first
    | (field_simp; ring)
    | field_simp

#print axioms integral_sub_rpow_neg_half
#print axioms sqrt_pi_div_arg
#print axioms sqrtConstant_le_rpow
#print axioms integral_rpow_dominant

end

end RHFormalization
