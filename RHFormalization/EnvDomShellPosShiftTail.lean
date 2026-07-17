import Mathlib
import RHFormalization.EnvDomShellPosHead
import RHFormalization.EnvDomShellPosTail
import RHFormalization.EnvDomShellSummable
set_option autoImplicit false
open Real Finset

namespace RHFormalization

/-- Shifted-tail bound: `∑'_k f(k+N) ≤ Kbound₄` when `N ≥ 2u`, since every shifted
index `k+N ≥ N ≥ 2u` puts the term in the convergent tail regime. -/
theorem shell_pos_shifted_tail_le
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : 0 < u) (N : ℕ) (hN : 2 * u ≤ (N : ℝ)) :
    ∑' k : ℕ, ((((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
        * Real.exp (-κ' * (u - ((k + N : ℕ) : ℝ)) ^ 2))
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
  have hκ'4 : 0 < κ' / 4 := by linarith
  have hsumm4 : Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
      * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2)) := summable_shell_coeff (κ' / 4) hκ'4
  -- each shifted term ≤ the κ'/4 coefficient at index (k+N), and that series is a
  -- subseries (tail) of the summable κ'/4 series; but we compare termwise to index k.
  -- Simpler: shifted term at k ≤ κ'/4-coeff at (k+N) ≤ κ'/4-coeff summed. Use tail ≤ whole.
  have hle : ∀ k : ℕ,
      (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
        * Real.exp (-κ' * (u - ((k + N : ℕ) : ℝ)) ^ 2)
      ≤ (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
          * Real.exp (-(κ' / 4) * ((k + N : ℕ) : ℝ) ^ 2) := by
    intro k
    have hkN2u : 2 * u ≤ ((k + N : ℕ) : ℝ) := by
      have : (N : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
        have : N ≤ k + N := Nat.le_add_left N k
        exact_mod_cast this
      linarith
    exact shell_pos_tail_term_le κ' hκ' u hu (k + N) hkN2u
  have hnn : ∀ k : ℕ, 0 ≤ (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
        * Real.exp (-κ' * (u - ((k + N : ℕ) : ℝ)) ^ 2) := by intro k; positivity
  -- the shifted κ'/4 series is summable (tail of summable)
  have hsumm4shift : Summable (fun k : ℕ =>
      (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
        * Real.exp (-(κ' / 4) * ((k + N : ℕ) : ℝ) ^ 2)) := by
    have := (summable_nat_add_iff N).mpr hsumm4
    simpa using this
  have hsummLHS : Summable (fun k : ℕ =>
      (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
        * Real.exp (-κ' * (u - ((k + N : ℕ) : ℝ)) ^ 2)) :=
    Summable.of_nonneg_of_le hnn hle hsumm4shift
  calc ∑' k : ℕ, ((((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
          * Real.exp (-κ' * (u - ((k + N : ℕ) : ℝ)) ^ 2))
      ≤ ∑' k : ℕ, (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
          * Real.exp (-(κ' / 4) * ((k + N : ℕ) : ℝ) ^ 2) :=
        Summable.tsum_mono hsummLHS hsumm4shift hle
    _ ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
        rw [← Summable.sum_add_tsum_nat_add N hsumm4]
        have hpart : 0 ≤ ∑ k ∈ Finset.range N, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
            * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
          apply Finset.sum_nonneg; intro k _; positivity
        linarith [hpart]

#print axioms shell_pos_shifted_tail_le

end RHFormalization
