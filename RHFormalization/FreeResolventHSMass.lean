-- SENTINEL: HSMASS-v1
import RHFormalization.HilbertSchmidtTraceBound
import RHFormalization.FreeResolventMassBound
import Mathlib

/-!
# FreeResolventHSMass — the sharp (Hilbert–Schmidt) replacement for the mass step

CONSUMER: the `A`-argument of `abs_trace_mul_le_hs` (HSTRACE) in the sharpened
Z estimate → `hr` of `seam_bdd_of_parts` → GATE → RH.

  Σ ‖(s+λᵢ)⁻¹‖² ≤ δ⁻¹ · (banked mass bound)

Each term is ‖·‖·‖·‖ ≤ δ⁻¹·‖·‖, so the HS sum is δ⁻¹ times MASSBOUND's sum.
L-scaling: mass ~ L² but HS² ~ L, so ‖R_D‖_HS ~ √L and the 1/(2L) density
factor absorbs it — matching the measurement (|Z|/(2L) decaying, ratios
1.865 → 0.642 → 0.495).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

variable {N : ℕ}

/-- HS norm of a diagonal matrix is the ℓ² norm of its diagonal. -/
theorem hsNorm_diagonal (d : Fin N → ℂ) :
    hsNorm (Matrix.diagonal d) = Real.sqrt (∑ i, ‖d i‖ ^ 2) := by
  classical
  unfold hsNorm
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji)]
    simp
  · intro hni
    exact absurd (Finset.mem_univ i) hni

/-- **The HS mass bound**: sharper than MASSBOUND by a factor δ⁻¹ vs the sum. -/
theorem free_resolvent_hs_sq_le
    (lam : Fin N → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (s : ℂ) (M : ℝ) (hM : ‖s‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ i, δ ≤ ‖s + (lam i : ℂ)‖)
    {c : ℝ} (hc : 0 < c)
    (hgrow : ∀ i : Fin N, c * (((i : ℕ) : ℝ) + 1) ^ 2 ≤ lam i) :
    ∑ i, ‖(s + (lam i : ℂ))⁻¹‖ ^ 2
      ≤ δ⁻¹ * ((2 * (1 + M + δ) / δ)
          * ∑' n : ℕ, (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹) := by
  have hδ0 : (0:ℝ) ≤ δ⁻¹ := by positivity
  have hterm : ∀ i : Fin N,
      ‖(s + (lam i : ℂ))⁻¹‖ ^ 2 ≤ δ⁻¹ * ‖(s + (lam i : ℂ))⁻¹‖ := by
    intro i
    have hpos : (0:ℝ) < ‖s + (lam i : ℂ)‖ := lt_of_lt_of_le hδ (hlow i)
    have hbd : ‖(s + (lam i : ℂ))⁻¹‖ ≤ δ⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ hpos hδ).mpr (hlow i)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hbd (norm_nonneg _)
  have hmass := free_resolvent_mass_le lam hlam s M hM hδ hlow hc hgrow
  calc ∑ i, ‖(s + (lam i : ℂ))⁻¹‖ ^ 2
      ≤ ∑ i : Fin N, δ⁻¹ * ‖(s + (lam i : ℂ))⁻¹‖ :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = δ⁻¹ * ∑ i : Fin N, ‖(s + (lam i : ℂ))⁻¹‖ := by rw [Finset.mul_sum]
    _ ≤ δ⁻¹ * ((2 * (1 + M + δ) / δ)
          * ∑' n : ℕ, (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hmass hδ0

#print axioms hsNorm_diagonal
#print axioms free_resolvent_hs_sq_le

end

end RHFormalization
