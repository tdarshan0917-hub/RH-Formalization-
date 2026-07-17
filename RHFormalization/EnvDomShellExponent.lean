import Mathlib
import RHFormalization.EnvDomShellPosition
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, shell exponent transfer.** Given `b ≥ a − 1`, `0 ≤ a`, `0 ≤ b`,
and `0 < κ' < κ`, the exponents satisfy
`κ'·a² ≤ κ·b² + C` with `C = κ²/(κ−κ') + κ'`. Quadratic completion behind the
Gaussian localization (manuscript A.ENV-DOM p.54). -/
theorem shell_exponent_transfer
    (κ κ' : ℝ) (hκ' : 0 < κ') (hκκ' : κ' < κ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≥ a - 1) :
    κ' * a ^ 2 ≤ κ * b ^ 2 + (κ ^ 2 / (κ - κ') + κ') := by
  have hκ : 0 < κ := lt_trans hκ' hκκ'
  have hd : 0 < κ - κ' := by linarith
  have hCnn : (0:ℝ) ≤ κ ^ 2 / (κ - κ') := div_nonneg (sq_nonneg κ) (le_of_lt hd)
  rcases le_or_gt 1 a with h1 | h1
  · -- a ≥ 1: b ≥ a-1 ≥ 0 ⟹ (a-1)² ≤ b² ⟹ κb² ≥ κ(a-1)²; then quadratic completion
    have hbsq : (a - 1) ^ 2 ≤ b ^ 2 := by nlinarith [hab, h1]
    have hkb : κ * (a - 1) ^ 2 ≤ κ * b ^ 2 := by nlinarith [hbsq, hκ]
    have hcore : (κ - κ') * (κ' * a ^ 2 - κ * (a - 1) ^ 2 - κ') ≤ κ ^ 2 := by
      nlinarith [sq_nonneg ((κ - κ') * a - κ)]
    have hkey : κ' * a ^ 2 - κ * (a - 1) ^ 2 - κ' ≤ κ ^ 2 / (κ - κ') := by
      rw [le_div_iff₀ hd]; linarith [hcore]
    linarith [hkey, hkb]
  · -- a < 1: κ'a² ≤ κ' ≤ C, and κb² ≥ 0
    have ha1 : a ^ 2 ≤ 1 := by nlinarith [ha, h1]
    have hkbnn : (0:ℝ) ≤ κ * b ^ 2 := mul_nonneg (le_of_lt hκ) (sq_nonneg b)
    nlinarith [ha1, hκ', hkbnn, hCnn]

#print axioms shell_exponent_transfer

end RHFormalization
