import RHFormalization.ResolventTraceHolo
import RHFormalization.FiniteStageSpectrum

namespace RHFormalization
noncomputable section
open Complex Finset

variable {n : ℕ}

/-- **Denominator lower bound**: `|Im s| ≤ ‖s + λ‖` for real `λ`. -/
theorem abs_im_le_norm_add_real (s : ℂ) (lam : ℝ) :
    |Complex.im s| ≤ ‖s + (lam : ℂ)‖ := by
  have him : (s + (lam : ℂ)).im = s.im := by simp
  rw [← him]; exact abs_im_le_norm (s + (lam : ℂ))

/-- **Per-term resolvent bound** off the real axis: `‖(s+λ)⁻¹‖ ≤ 1/|Im s|`. -/
theorem resolvent_term_norm_le (s : ℂ) (hs : Complex.im s ≠ 0) (lam : ℝ) :
    ‖(s + (lam : ℂ))⁻¹‖ ≤ 1 / |Complex.im s| := by
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le (abs_pos.mpr hs) (abs_im_le_norm_add_real s lam)

/-- **Free F-stage resolvent compact bound.** Off the real axis, the finite resolvent
trace `∑ᵢ 1/(s+λᵢ)` is bounded by `n/|Im s|`. A genuine, sorry-free bound on the ACTUAL
resolvent (no designed-zero placeholder) — a real sector of the operator-side residual
estimate, at fixed stage `n`. -/
theorem FstageFinite_norm_le (s : ℂ) (hs : Complex.im s ≠ 0) (lam : Fin n → ℝ) :
    ‖FstageFinite lam s‖ ≤ n / |Complex.im s| := by
  unfold FstageFinite
  calc ‖∑ i, (s + (lam i : ℂ))⁻¹‖
      ≤ ∑ i, ‖(s + (lam i : ℂ))⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 / |Complex.im s|) :=
        Finset.sum_le_sum (fun i _ => resolvent_term_norm_le s hs (lam i))
    _ = n / |Complex.im s| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

#print axioms FstageFinite_norm_le
end
end RHFormalization
