import Mathlib
import RHFormalization.EnvDomShellTermBound
set_option autoImplicit false
open ArithmeticFunction Real Finset

namespace RHFormalization

/-- **A.ENV-DOM, shell sum bound.** For any finite set `S` of naturals all lying
in logarithmic shell `k` (each `q ∈ S` has `1 ≤ q`, `e^k ≤ q`, `log q < k+1`),
the total weight is bounded by the shell cardinality times the per-term maximum:
`∑_{q∈S} Λ(q)/q ≤ |S|·(k+1)·e^{-k}` (manuscript A.ENV-DOM p.54, shell-sum step). -/
theorem shell_sum_weight_le
    (k : ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, 1 ≤ q ∧ Real.exp k ≤ q ∧ Real.log q < (k : ℝ) + 1) :
    ∑ q ∈ S, (vonMangoldt q : ℝ) / q
      ≤ (S.card : ℝ) * (((k : ℝ) + 1) * Real.exp (-(k : ℝ))) := by
  have hterm : ∀ q ∈ S,
      (vonMangoldt q : ℝ) / q ≤ ((k : ℝ) + 1) * Real.exp (-(k : ℝ)) := by
    intro q hq
    obtain ⟨hq1, hlo, hhi⟩ := hS q hq
    exact shell_term_weight_le k q hq1 hlo hhi
  calc ∑ q ∈ S, (vonMangoldt q : ℝ) / q
      ≤ S.card • (((k : ℝ) + 1) * Real.exp (-(k : ℝ))) :=
        sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (((k : ℝ) + 1) * Real.exp (-(k : ℝ))) := by
        rw [nsmul_eq_mul]

#print axioms shell_sum_weight_le

end RHFormalization
