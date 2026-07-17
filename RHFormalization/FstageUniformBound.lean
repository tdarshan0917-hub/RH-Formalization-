import RHFormalization.CorrectedResolventPayload
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Finset

/-- **Per-term resolvent bound via eigenvalue size.** For nonneg real `lam` with
`‖s‖ < lam`, the resolvent term is bounded by `1/(lam - ‖s‖)`. As `lam = (kπ)²`
grows this gives a CONVERGENT majorant `~1/(kπ)²`, independent of how many terms. -/
theorem resolvent_term_le_of_lt (s : ℂ) (lam : ℝ) (hlam : ‖s‖ < lam) :
    ‖(s + (lam : ℂ))⁻¹‖ ≤ 1 / (lam - ‖s‖) := by
  have hlam_nonneg : (0:ℝ) ≤ lam := le_of_lt (lt_of_le_of_lt (norm_nonneg s) hlam)
  have hpos : 0 < lam - ‖s‖ := by linarith
  have hden : lam - ‖s‖ ≤ ‖s + (lam : ℂ)‖ := by
    have h1 : ‖(lam : ℂ)‖ - ‖s‖ ≤ ‖(lam : ℂ) + s‖ := by
      have := norm_sub_norm_le ((lam : ℂ)) (-s)
      simpa [sub_neg_eq_add] using this
    have h2 : ‖(lam : ℂ)‖ = lam := by
      rw [Complex.norm_real]; exact abs_of_nonneg hlam_nonneg
    rw [h2] at h1
    rwa [add_comm] at h1
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hden

#print axioms resolvent_term_le_of_lt
end
end RHFormalization
