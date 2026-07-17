import Mathlib
set_option autoImplicit false
open ArithmeticFunction Real

namespace RHFormalization

/-- **A.ENV-DOM, shell weight rung.** For `q ≥ 1`, the von Mangoldt weight
`Λ(q)/q` is bounded by `log q / q` (manuscript A.ENV-DOM p.54). -/
theorem vonMangoldt_div_le_log_div (q : ℕ) (hq : 1 ≤ q) :
    (vonMangoldt q : ℝ) / q ≤ Real.log q / q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  gcongr
  exact vonMangoldt_le_log

/-- **Shell lower-endpoint decay.** For `q ≥ e^k`, `1/q ≤ e^{-k}`. This is the
lower-endpoint half of the shell weight bound (manuscript p.54). -/
theorem one_div_le_exp_neg_of_shell (k : ℕ) (q : ℕ)
    (hq : Real.exp k ≤ q) :
    (1 : ℝ) / q ≤ Real.exp (-(k : ℝ)) := by
  have hexppos : (0 : ℝ) < Real.exp k := Real.exp_pos _
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hexppos hq

#print axioms vonMangoldt_div_le_log_div
#print axioms one_div_le_exp_neg_of_shell

end RHFormalization
