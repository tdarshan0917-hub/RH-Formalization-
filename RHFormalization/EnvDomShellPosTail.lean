import Mathlib
import RHFormalization.EnvDomShellSummable
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, u>0 tail position bound.** For `u > 0` and `k ≥ 2u`, the
displacement satisfies `(u−k)² ≥ k²/4`. Since `k ≥ 2u > 0`, `k − u ≥ k/2`, so
`(k−u)² ≥ k²/4` (manuscript p.55, tail of the `u>0` shell sum). -/
theorem shell_pos_tail_position
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : 2 * u ≤ (k : ℝ)) :
    (u - (k : ℝ)) ^ 2 ≥ (k : ℝ) ^ 2 / 4 := by
  have hku : (k : ℝ) - u ≥ (k : ℝ) / 2 := by linarith
  have hk2 : (k : ℝ) / 2 ≥ 0 := by linarith
  nlinarith [hku, hk2]

/-- **A.ENV-DOM, u>0 tail term bound.** For `u > 0` and `k ≥ 2u`, the shell term
is dominated by the summable coefficient with `c = κ'/4`:
`(k+1)·e^{k/2}·e^{-κ'(u−k)²} ≤ (k+1)·e^{k/2}·e^{-(κ'/4)·k²}`. Combined with
`summable_shell_coeff (κ'/4)`, the tail converges (manuscript p.55). -/
theorem shell_pos_tail_term_le
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : 2 * u ≤ (k : ℝ)) :
    ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
  have hpos := shell_pos_tail_position u hu k hk
  have hexp : Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hpos, hκ']
  have hcoef : (0:ℝ) ≤ ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) := by positivity
  exact mul_le_mul_of_nonneg_left hexp hcoef

#print axioms shell_pos_tail_position
#print axioms shell_pos_tail_term_le

end RHFormalization
