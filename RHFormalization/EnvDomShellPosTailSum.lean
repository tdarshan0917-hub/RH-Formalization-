import Mathlib
import RHFormalization.EnvDomShellPosTail
import RHFormalization.EnvDomShellSummable
set_option autoImplicit false
open Real Finset

namespace RHFormalization

/-- **A.ENV-DOM, u>0 tail tsum bound.** The tail sum (each term replaced by its
`κ'/4`-dominated bound when `2u ≤ k`, else `≤` that bound trivially) is bounded
by the absolute `c = κ'/4` shell constant. Convergent tail of the `u>0` shell
sum (manuscript p.55). We bound the *masked* term `g k` that equals the real
term for `2u ≤ k` and `0` otherwise; `g k ≤ (k+1)e^{k/2}e^{-(κ'/4)k²}` for all k. -/
theorem shell_pos_tail_tsum_le
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : 0 < u) :
    ∑' k : ℕ, (if 2 * u ≤ (k : ℝ)
        then ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        else 0)
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
  have hκ'4 : 0 < κ' / 4 := by linarith
  have hsumm4 : Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
      * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2)) := summable_shell_coeff (κ' / 4) hκ'4
  have hle : ∀ k : ℕ,
      (if 2 * u ≤ (k : ℝ)
        then ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        else 0)
      ≤ ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
    intro k
    split_ifs with hk
    · exact shell_pos_tail_term_le κ' hκ' u hu k hk
    · positivity
  have hnn : ∀ k : ℕ, 0 ≤ (if 2 * u ≤ (k : ℝ)
        then ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        else 0) := by
    intro k; split_ifs with hk
    · positivity
    · exact le_refl 0
  have hsummg : Summable (fun k : ℕ => if 2 * u ≤ (k : ℝ)
        then ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        else 0) :=
    Summable.of_nonneg_of_le hnn hle hsumm4
  exact Summable.tsum_mono hsummg hsumm4 hle

#print axioms shell_pos_tail_tsum_le

end RHFormalization
