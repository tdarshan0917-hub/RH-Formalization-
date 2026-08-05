import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# RHFormalization.ResolventSqModulusDomination
**Brick 1 of the hSC assembly: complex-modulus domination of the squared
resolvent.** For `0 < s.re` and `0 ≤ λ`:
`‖((s+λ)²)⁻¹‖ ≤ ((s.re+λ)²)⁻¹`.
Carries the real-axis P2 chain (density−osc ≤ halfLine + crushed error)
onto Ω-compacts at `t = s.re`-floor, mode by mode.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- `(s.re+λ)² ≤ ‖s+λ‖²` for real `λ`. -/
theorem re_add_sq_le_norm_add_sq (s : ℂ) (lam : ℝ) :
    (s.re + lam) ^ 2 ≤ ‖s + (lam : ℂ)‖ ^ 2 := by
  have hnsq : ‖s + (lam : ℂ)‖ ^ 2 = (s.re + lam) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hnsq]
  nlinarith [sq_nonneg s.im]

/-- **Brick 1: squared-resolvent modulus domination.** -/
theorem resolventSq_inv_norm_le (s : ℂ) (lam : ℝ)
    (hs : 0 < s.re) (hlam : 0 ≤ lam) :
    ‖(((s + (lam : ℂ)) ^ 2)⁻¹ : ℂ)‖ ≤ ((s.re + lam) ^ 2)⁻¹ := by
  have hfloor : (0:ℝ) < s.re + lam := by linarith
  have hfloor2 : (0:ℝ) < (s.re + lam) ^ 2 := by positivity
  have hle : (s.re + lam) ^ 2 ≤ ‖s + (lam : ℂ)‖ ^ 2 :=
    re_add_sq_le_norm_add_sq s lam
  have hnormsq : ‖((s + (lam : ℂ)) ^ 2 : ℂ)‖ = ‖s + (lam : ℂ)‖ ^ 2 :=
    norm_pow _ 2
  rw [norm_inv, hnormsq]
  rw [inv_eq_one_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) hfloor2 hle

#print axioms re_add_sq_le_norm_add_sq
#print axioms resolventSq_inv_norm_le

end

end RHFormalization
