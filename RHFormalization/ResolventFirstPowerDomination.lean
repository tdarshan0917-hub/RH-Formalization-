import RHFormalization.ResolventSqModulusDomination

/-!
# RHFormalization.ResolventFirstPowerDomination
**Main-term twin 1: first-power resolvent modulus domination.**
`‖(s+1/4+λ)⁻¹‖ ≤ (s.re+1/4+λ)⁻¹` for `−1/4 < s.re`, `0 ≤ λ` — the
first-power sibling of the banked `resolventSq_inv_norm_le`, feeding the
hT main-term mode sum.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- First-power domination at the shifted point. -/
theorem resolvent_shift_inv_norm_le (s : ℂ) (lam : ℝ)
    (hs : -(1/4 : ℝ) < s.re) (hlam : 0 ≤ lam) :
    ‖((s + (1/4 : ℂ) + (lam : ℂ))⁻¹ : ℂ)‖
      ≤ ((s.re + 1/4 + lam))⁻¹ := by
  have hre : (s + (1/4 : ℂ) + (lam : ℂ)).re = s.re + 1/4 + lam := by
    simp [Complex.add_re, Complex.ofReal_re]
  have hfloor : (0:ℝ) < s.re + 1/4 + lam := by linarith
  have hle : s.re + 1/4 + lam ≤ ‖s + (1/4 : ℂ) + (lam : ℂ)‖ := by
    rw [← hre]
    exact Complex.re_le_norm _
  rw [norm_inv]
  rw [inv_eq_one_div, inv_eq_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) hfloor hle

#print axioms resolvent_shift_inv_norm_le

end

end RHFormalization
