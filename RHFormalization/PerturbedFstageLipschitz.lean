import RHFormalization.ResolventTraceHolo
import RHFormalization.PerturbedEigenvalueWeyl
import RHFormalization.PerturbedResidual

namespace RHFormalization
noncomputable section
open Complex Finset

variable {n : ℕ}

/-- Per-term resolvent difference: `‖1/(s+a) − 1/(s+b)‖ = ‖b−a‖/(‖s+a‖·‖s+b‖)` on Ω. -/
theorem resolvent_term_diff (s : ℂ) (hs : s ∈ Ω) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(s + (a:ℂ))⁻¹ - (s + (b:ℂ))⁻¹‖
      = ‖(b:ℂ) - (a:ℂ)‖ / (‖s + (a:ℂ)‖ * ‖s + (b:ℂ)‖) := by
  have hsa : s + (a:ℂ) ≠ 0 := add_real_ne_zero_of_mem_Omega hs ha
  have hsb : s + (b:ℂ) ≠ 0 := add_real_ne_zero_of_mem_Omega hs hb
  rw [inv_sub_inv hsa hsb, norm_div, norm_mul]
  congr 1
  rw [show (s + (b:ℂ)) - (s + (a:ℂ)) = (b:ℂ) - (a:ℂ) by ring]

/-- **F-stage is Lipschitz in its eigenvalues, pointwise on Ω.**
`‖FstageFinite λ₁ s − FstageFinite λ₂ s‖ ≤ ∑ᵢ ‖λ₂ᵢ−λ₁ᵢ‖/(‖s+λ₁ᵢ‖·‖s+λ₂ᵢ‖)`. -/
theorem FstageFinite_diff_le (s : ℂ) (hs : s ∈ Ω)
    (lam1 lam2 : Fin n → ℝ) (h1 : ∀ i, 0 ≤ lam1 i) (h2 : ∀ i, 0 ≤ lam2 i) :
    ‖FstageFinite lam1 s - FstageFinite lam2 s‖
      ≤ ∑ i, ‖(lam2 i : ℂ) - (lam1 i : ℂ)‖
          / (‖s + (lam1 i : ℂ)‖ * ‖s + (lam2 i : ℂ)‖) := by
  unfold FstageFinite
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro i _
  rw [resolvent_term_diff s hs (h1 i) (h2 i)]
