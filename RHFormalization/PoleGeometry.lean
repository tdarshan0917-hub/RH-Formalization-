import RHFormalization.Basic

/-!
# RHFormalization.PoleGeometry

Iteration 2: formalize the Appendix-F pole geometry.
-/
namespace RHFormalization
noncomputable section
open Complex

theorem lambda_re_formula (ρ : ℂ) :
    (ρ * (1 - ρ)).re = ρ.re * (1 - ρ.re) + ρ.im ^ 2 := by
  simp [Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.mul_im, Complex.sub_im, Complex.one_im]
  ring

theorem lambda_im_formula (ρ : ℂ) :
    (ρ * (1 - ρ)).im = ρ.im * (1 - 2 * ρ.re) := by
  simp [Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.mul_im, Complex.sub_im, Complex.one_im]
  ring

theorem polePoint_re_formula (ρ : ℂ) :
    (polePoint ρ).re = - (ρ.re * (1 - ρ.re) + ρ.im ^ 2) := by
  unfold polePoint
  rw [Complex.neg_re]
  rw [lambda_re_formula]

theorem polePoint_im_formula (ρ : ℂ) :
    (polePoint ρ).im = ρ.im * (2 * ρ.re - 1) := by
  unfold polePoint
  rw [Complex.neg_im]
  rw [lambda_im_formula]
  ring

theorem offLine_zeroPolePoint_in_Omega
    (ZF : ZetaZeroFacts) {ρ : ℂ}
    (h_zero : IsNontrivialZetaZero ρ)
    (h_off : ρ.re ≠ (1 / 2 : ℝ)) :
    zeroPolePoint ρ ∈ Ω := by
  rw [zeroPolePoint, mem_Omega_iff]
  intro h_cut
  have h_im_cut : (polePoint ρ).im = 0 := h_cut.1
  have h_im_formula : (polePoint ρ).im = ρ.im * (2 * ρ.re - 1) :=
    polePoint_im_formula ρ
  have h_product_zero : ρ.im * (2 * ρ.re - 1) = 0 := by
    rw [← h_im_formula]
    exact h_im_cut
  have h_gamma : ρ.im ≠ 0 := ZF.nontrivial_zero_im_ne_zero ρ h_zero
  have h_factor : (2 * ρ.re - 1) ≠ 0 := by
    intro h
    apply h_off
    linarith
  exact (mul_ne_zero h_gamma h_factor) h_product_zero

theorem criticalLine_polePoint_on_cut {ρ : ℂ}
    (h_crit : ρ.re = (1 / 2 : ℝ)) :
    polePoint ρ ∈ NonpositiveRealAxis := by
  constructor
  · rw [polePoint_im_formula]
    rw [h_crit]
    norm_num
  · rw [polePoint_re_formula]
    rw [h_crit]
    have hsq : 0 ≤ ρ.im ^ 2 := sq_nonneg ρ.im
    nlinarith

theorem criticalLine_zeroPolePoint_not_in_Omega {ρ : ℂ}
    (h_crit : ρ.re = (1 / 2 : ℝ)) :
    zeroPolePoint ρ ∉ Ω := by
  rw [zeroPolePoint, mem_Omega_iff]
  intro h
  exact h (criticalLine_polePoint_on_cut h_crit)

end
end RHFormalization
