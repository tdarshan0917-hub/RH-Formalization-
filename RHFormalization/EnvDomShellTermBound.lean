import Mathlib
import RHFormalization.EnvDomShellWeight
set_option autoImplicit false
open ArithmeticFunction Real Finset

namespace RHFormalization

/-- **A.ENV-DOM, per-term shell bound.** For `q` in logarithmic shell `k`
(`e^k ≤ q` and `log q < k+1`), the weight `Λ(q)/q` is bounded by
`(k+1)·e^{-k}`. Combines the weight bound `Λ(q)/q ≤ log q/q` with
`log q < k+1` and `1/q ≤ e^{-k}` (manuscript A.ENV-DOM p.54). -/
theorem shell_term_weight_le
    (k : ℕ) (q : ℕ) (hq1 : 1 ≤ q)
    (hlo : Real.exp k ≤ q) (hhi : Real.log q < (k : ℝ) + 1) :
    (vonMangoldt q : ℝ) / q ≤ ((k : ℝ) + 1) * Real.exp (-(k : ℝ)) := by
  -- Λ(q)/q ≤ log q / q  = log q · (1/q) ≤ (k+1) · e^{-k}
  have hstep1 : (vonMangoldt q : ℝ) / q ≤ Real.log q / q :=
    vonMangoldt_div_le_log_div q hq1
  have hlogpos : 0 ≤ Real.log q := by
    have : (1:ℝ) ≤ q := by exact_mod_cast hq1
    exact Real.log_nonneg this
  have hinv : (1 : ℝ) / q ≤ Real.exp (-(k : ℝ)) :=
    one_div_le_exp_neg_of_shell k q hlo
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
  calc (vonMangoldt q : ℝ) / q
      ≤ Real.log q / q := hstep1
    _ = Real.log q * (1 / q) := by rw [mul_one_div]
    _ ≤ ((k : ℝ) + 1) * Real.exp (-(k : ℝ)) := by
        apply mul_le_mul (le_of_lt hhi) hinv (by positivity) (by positivity)

#print axioms shell_term_weight_le

end RHFormalization
