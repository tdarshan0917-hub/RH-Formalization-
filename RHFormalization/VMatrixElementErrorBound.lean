import RHFormalization.PrimePotentialBumpSplit
import RHFormalization.BumpMatrixElementErrorBound
import RHFormalization.CosBumpIntegralFull
set_option autoImplicit false
open MeasureTheory Real Set Finset

namespace RHFormalization

/-- The closed-form value of the bump matrix element at `(m,n)` for prime `q`:
`½·Full(m−n) − ½·Full(m+n)`. -/
noncomputable def bumpClosed (δ : ℝ) (q : ℕ) (L : ℝ) (m n : ℕ) : ℝ :=
  (1/2) * cosBumpIntegralFull δ q L ((m : ℝ) - n)
    - (1/2) * cosBumpIntegralFull δ q L ((m : ℝ) + n)

/-- **B11 — lift the error bound to `VmatrixElement`.** The genuine matrix element
differs from the weighted sum of closed forms by at most the weighted sum of the
per-prime Gaussian-tail decay bounds. -/
theorem VmatrixElement_sub_closedSum_norm_le
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ)
    (hq : ∀ q ∈ qs, 0 < Real.log q) (hL : ∀ q ∈ qs, Real.log q < L) :
    ‖VmatrixElement δ qs w L m n
        - ∑ q ∈ qs, w q * bumpClosed δ q L m n‖
      ≤ ∑ q ∈ qs, ‖w q‖ * gaussianDecayBound δ q L := by
  rw [VmatrixElement_eq_sum_bumps]
  -- combine the two sums: ∑ w q·bump − ∑ w q·closed = ∑ w q·(bump − closed)
  have hcombine :
      (∑ q ∈ qs, w q * bumpMatrixElement δ q L m n)
        - ∑ q ∈ qs, w q * bumpClosed δ q L m n
      = ∑ q ∈ qs, w q * (bumpMatrixElement δ q L m n - bumpClosed δ q L m n) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hcombine]
  -- ‖∑‖ ≤ ∑‖·‖
  refine le_trans (norm_sum_le _ _) ?_
  -- per-term: ‖w q·(bump − closed)‖ ≤ ‖w q‖·gaussianDecayBound
  apply Finset.sum_le_sum
  intro q hqmem
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  -- ‖bump − closed‖ ≤ gaussianDecayBound  (B10, unfolding bumpClosed)
  have hB10 := bumpMatrixElement_sub_closed_norm_le δ hδ q L m n (hq q hqmem) (hL q hqmem)
  simpa [bumpClosed] using hB10

end RHFormalization
