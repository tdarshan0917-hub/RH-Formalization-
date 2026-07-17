import Mathlib
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **Polynomial-vs-exponential helper.** For `x ≥ 0`, `x² ≤ 4·e^x`.
From `1 + x/2 ≤ e^{x/2}` (add_one_le_exp), square the nonneg sides to get
`(1+x/2)² ≤ e^x`; since `(1+x/2)² = 1 + x + x²/4`, this gives `x² ≤ 4·e^x`.
Feeds the u>0 envelope combine (turns `u²·e^{u/2}` growth into `≤ C·e^u`). -/
theorem sq_le_four_mul_exp (x : ℝ) (hx : 0 ≤ x) : x ^ 2 ≤ 4 * Real.exp x := by
  have hhalf : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2); linarith
  have hnn : (0:ℝ) ≤ 1 + x / 2 := by linarith
  have hsq : (1 + x / 2) ^ 2 ≤ (Real.exp (x / 2)) ^ 2 := by
    apply sq_le_sq' <;> nlinarith [hhalf, hnn, Real.exp_pos (x / 2)]
  have hexp2 : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hexp2] at hsq
  nlinarith [hsq, hx, sq_nonneg (x / 2)]

#print axioms sq_le_four_mul_exp

end RHFormalization
