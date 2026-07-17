import Mathlib
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, u>0 exponent bound.** The shell exponent, after the substitution
`j = k − u`, satisfies `k/2 − κ'(u−k)² ≤ u/2 + 1/(16κ')`. The `j`-part
`j/2 − κ'j²` is maximized at `j = 1/(4κ')` with value `1/(16κ')`
(manuscript p.55, `u>0` case). -/
theorem shell_pos_exponent_bound
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (k : ℕ) :
    (k : ℝ) / 2 - κ' * (u - (k : ℝ)) ^ 2 ≤ u / 2 + 1 / (16 * κ') := by
  -- with j = k - u: k/2 - κ'(u-k)² = u/2 + j/2 - κ'j², and j/2 - κ'j² ≤ 1/(16κ')
  -- since κ'(j - 1/(4κ'))² ≥ 0 expands to κ'j² - j/2 + 1/(16κ') ≥ 0.
  have hsq : 0 ≤ κ' * (((k : ℝ) - u) - 1 / (4 * κ')) ^ 2 :=
    mul_nonneg (le_of_lt hκ') (sq_nonneg _)
  have hexpand : κ' * (((k : ℝ) - u) - 1 / (4 * κ')) ^ 2
      = κ' * ((k : ℝ) - u) ^ 2 - ((k : ℝ) - u) / 2 + 1 / (16 * κ') := by
    field_simp; ring
  nlinarith [hsq, hexpand]

#print axioms shell_pos_exponent_bound

end RHFormalization
