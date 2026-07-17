import Mathlib
import RHFormalization.EnvDomShellPosition
import RHFormalization.EnvDomShellExponent
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, Gaussian localization.** For `q` in logarithmic shell `k`
(`k ≤ log q < k+1`) and `0 < κ' < κ`, the Gaussian centered at the prime
position `log q` is dominated by a constant multiple of the Gaussian centered
at the integer shell index `k`:
`exp(−κ·(u−log q)²) ≤ exp(C)·exp(−κ'·(u−k)²)` with `C = κ²/(κ−κ') + κ'`
(manuscript A.ENV-DOM p.54). -/
theorem shell_gaussian_localization
    (κ κ' : ℝ) (hκ' : 0 < κ') (hκκ' : κ' < κ)
    (k : ℕ) (u : ℝ) (lq : ℝ)
    (hlo : (k : ℝ) ≤ lq) (hhi : lq < (k : ℝ) + 1) :
    Real.exp (-κ * (u - lq) ^ 2)
      ≤ Real.exp (κ ^ 2 / (κ - κ') + κ') * Real.exp (-κ' * (u - (k : ℝ)) ^ 2) := by
  set a : ℝ := |u - (k : ℝ)| with ha_def
  set b : ℝ := |u - lq| with hb_def
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hab : b ≥ a - 1 := by
    rw [ha_def, hb_def]; exact shell_position_bound k u lq hlo hhi
  -- exponent inequality: κ'a² ≤ κb² + C
  have hexp := shell_exponent_transfer κ κ' hκ' hκκ' a b ha hb hab
  -- squares: (u-lq)² = b², (u-k)² = a²
  have hbsq : (u - lq) ^ 2 = b ^ 2 := by rw [hb_def, sq_abs]
  have hasq : (u - (k : ℝ)) ^ 2 = a ^ 2 := by rw [ha_def, sq_abs]
  rw [hbsq, hasq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- -κb² ≤ (C) + (-κ'a²)   ⟺   κ'a² ≤ κb² + C
  linarith [hexp]

#print axioms shell_gaussian_localization

end RHFormalization
