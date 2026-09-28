import RHFormalization.DenseDiagLowFreqSplit
import Mathlib

/-!
# DenseTwoModeCos — KB3b-i: two-mode cosine inequality

`cos²θ + cos²(θ + π/2 + η) ≥ 1 − 2|η|`.  Two Galerkin modes whose phases differ by
approximately a quarter turn together carry at least half the amplitude, whatever the
unknown phase θ.  This replaces any Riemann-sum averaging in the B8 kill theorem.
-/

set_option autoImplicit false

namespace RHFormalization

theorem abs_sin_le_abs' (t : ℝ) : |Real.sin t| ≤ |t| := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]; exact abs_sin_le_self_of_nonneg h
  · have h' : 0 ≤ -t := by linarith
    have := abs_sin_le_self_of_nonneg h'
    rw [Real.sin_neg, abs_neg] at this
    rw [abs_of_neg h]; exact this

theorem abs_sin_sub_sin_le' (x y : ℝ) : |Real.sin x - Real.sin y| ≤ |x - y| := by
  rw [Real.sin_sub_sin]
  rw [abs_mul, abs_mul]
  have h1 : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := abs_sin_le_abs' _
  have h2 : |Real.cos ((x + y) / 2)| ≤ 1 := Real.abs_cos_le_one _
  calc |(2:ℝ)| * |Real.sin ((x - y) / 2)| * |Real.cos ((x + y) / 2)|
      ≤ |(2:ℝ)| * |(x - y) / 2| * 1 := by gcongr
    _ = |x - y| := by rw [abs_div, abs_two]; ring

/-- **KB3b-i**: two modes a quarter-turn apart (up to `η`) carry at least `1 − 2|η|`. -/
theorem cos_sq_add_cos_sq_quarter_ge (θ η : ℝ) :
    Real.cos θ ^ 2 + Real.cos (θ + Real.pi / 2 + η) ^ 2 ≥ 1 - 2 * |η| := by
  have hc : Real.cos (θ + Real.pi / 2 + η) = -Real.sin (θ + η) := by
    rw [show θ + Real.pi / 2 + η = (θ + η) + Real.pi / 2 by ring]
    exact Real.cos_add_pi_div_two _
  rw [hc, neg_sq]
  have hpyth : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hlip : |Real.sin (θ + η) - Real.sin θ| ≤ |η| := by
    have := abs_sin_sub_sin_le' (θ + η) θ
    rwa [show θ + η - θ = η by ring] at this
  have hsum : |Real.sin (θ + η) + Real.sin θ| ≤ 2 := by
    calc _ ≤ |Real.sin (θ + η)| + |Real.sin θ| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  have hdiff : |Real.sin (θ + η) ^ 2 - Real.sin θ ^ 2| ≤ 2 * |η| := by
    rw [sq_sub_sq, abs_mul]
    first
      | exact mul_le_mul hsum hlip (abs_nonneg _) (by norm_num)
      | (rw [mul_comm]; exact mul_le_mul hsum hlip (abs_nonneg _) (by norm_num))
  have := (abs_le.mp hdiff).1
  nlinarith [hpyth, this]

#print axioms cos_sq_add_cos_sq_quarter_ge

end RHFormalization
