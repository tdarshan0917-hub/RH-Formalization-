import Mathlib
import RHFormalization.EnvDomShellSummable
import RHFormalization.EnvDomShellNegCase
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, u≤0 shell-sum bound.** For `u ≤ 0` and `0 < κ'`, the full shell
sum is bounded by a constant (independent of `u`):
`∑'_k (k+1)·e^{k/2}·e^{-κ'(u−k)²} ≤ ∑'_k (k+1)·e^{k/2}·e^{-κ'k²}`.
The `u`-dependence factors as `e^{-κ'u²} ≤ 1`, leaving the summable coefficient
series (manuscript p.55, `u≤0` case, giving `≤ C`). -/
theorem shell_neg_tsum_le
    (u : ℝ) (hu : u ≤ 0) (κ' : ℝ) (hκ' : 0 < κ') :
    ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (k : ℝ) ^ 2) := by
  -- both series summable
  have hsummR : Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
      * Real.exp (-κ' * (k : ℝ) ^ 2)) := summable_shell_coeff κ' hκ'
  -- the u-shifted series is dominated termwise, hence summable and ≤
  have hle : ∀ k : ℕ,
      ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (k : ℝ) ^ 2) := by
    intro k
    -- e^{-κ'(u-k)²} ≤ e^{-κ'u²}·e^{-κ'k²} ≤ 1·e^{-κ'k²} = e^{-κ'k²}
    have hfac := shell_neg_gaussian_factor u hu k κ' hκ'
    have hu1 : Real.exp (-κ' * u ^ 2) ≤ 1 := by
      rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg u, hκ']
    have hstep : Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ Real.exp (-κ' * (k : ℝ) ^ 2) := by
      calc Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
          ≤ Real.exp (-κ' * u ^ 2) * Real.exp (-κ' * (k : ℝ) ^ 2) := hfac
        _ ≤ 1 * Real.exp (-κ' * (k : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_right hu1 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-κ' * (k : ℝ) ^ 2) := one_mul _
    have hcoef : (0:ℝ) ≤ ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) := by positivity
    exact mul_le_mul_of_nonneg_left hstep hcoef
  -- summability of the shifted series via comparison
  have hsummU : Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
      * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)) := by
    apply Summable.of_nonneg_of_le (fun k => by positivity) hle hsummR
  exact Summable.tsum_mono hsummU hsummR hle

#print axioms shell_neg_tsum_le

end RHFormalization
