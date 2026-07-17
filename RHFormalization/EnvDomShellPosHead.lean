import Mathlib
import RHFormalization.EnvDomShellPosExp
import RHFormalization.EnvDomShellPosFactor
set_option autoImplicit false
open Real Finset

namespace RHFormalization

/-- **A.ENV-DOM, u>0 head per-term bound.** For `u > 0` and any `k`, the shell
term is bounded by `(k+1)·exp(u/2 + 1/(16κ'))`, dropping the Gaussian localization
via the exponent bound `k/2 − κ'(u−k)² ≤ u/2 + 1/(16κ')`
(banked `shell_pos_exponent_bound`). Used for the finite head `k < 2u`
(manuscript p.55). -/
theorem shell_pos_head_term_le
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ ((k : ℝ) + 1) * Real.exp (u / 2 + 1 / (16 * κ')) := by
  rw [shell_pos_term_factor κ' hκ' u k]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact shell_pos_exponent_bound κ' hκ' u k

/-- **A.ENV-DOM, u>0 head sum bound.** The finite head sum over `k ∈ range N`
is bounded by `N · N · exp(u/2 + 1/(16κ'))` (each of the `N` terms has
`k+1 ≤ N` when `k < N`, and the exponential factor is uniform). For the head
`N = ⌈2u⌉`, this gives `≤ C·u²·e^{u/2}`, absorbed by the envelope
(manuscript p.55). -/
theorem shell_pos_head_sum_le
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N,
        ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ (N : ℝ) * ((N : ℝ) * Real.exp (u / 2 + 1 / (16 * κ'))) := by
  have hterm : ∀ k ∈ Finset.range N,
      ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ (N : ℝ) * Real.exp (u / 2 + 1 / (16 * κ')) := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by
      have hkN_nat : k + 1 ≤ N := Finset.mem_range.mp hk
      exact_mod_cast hkN_nat
    calc ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ ((k : ℝ) + 1) * Real.exp (u / 2 + 1 / (16 * κ')) :=
          shell_pos_head_term_le κ' hκ' u k
      _ ≤ (N : ℝ) * Real.exp (u / 2 + 1 / (16 * κ')) := by
          apply mul_le_mul_of_nonneg_right hkN (le_of_lt (Real.exp_pos _))
  calc ∑ k ∈ Finset.range N,
          ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ ∑ _k ∈ Finset.range N, (N : ℝ) * Real.exp (u / 2 + 1 / (16 * κ')) :=
        Finset.sum_le_sum hterm
    _ = (Finset.range N).card • ((N : ℝ) * Real.exp (u / 2 + 1 / (16 * κ'))) := by
        rw [Finset.sum_const]
    _ = (N : ℝ) * ((N : ℝ) * Real.exp (u / 2 + 1 / (16 * κ'))) := by
        rw [Finset.card_range, nsmul_eq_mul]

#print axioms shell_pos_head_term_le
#print axioms shell_pos_head_sum_le

end RHFormalization
