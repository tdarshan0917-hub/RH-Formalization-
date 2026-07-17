import RHFormalization.BumpMatrixElementCosForm
import RHFormalization.CosBumpIntegralFull
import RHFormalization.CosBumpIntegralErrorBound
set_option autoImplicit false
open MeasureTheory Real Set

namespace RHFormalization

/-- Abbreviation for the Gaussian-tail decay bound at frequency `j` (the RHS of B9). -/
noncomputable def gaussianDecayBound (δ : ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  (1 / Real.sqrt (2*Real.pi*δ^2))
      * (Real.exp (-(1/(2*δ^2) * (Real.log q)^2)) / ((1/(2*δ^2)) * Real.log q))
    + (1 / Real.sqrt (2*Real.pi*δ^2))
      * (Real.exp (-(1/(2*δ^2) * (L - Real.log q)^2)) / ((1/(2*δ^2)) * (L - Real.log q)))

/-- **B10 — lift the error bound to `bumpMatrixElement`.** The bump matrix element
differs from its closed-form value (`½·Full(m−n) − ½·Full(m+n)`) by at most the sum
of the two Gaussian-tail decay bounds (one per frequency `m−n`, `m+n`). -/
theorem bumpMatrixElement_sub_closed_norm_le
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (m n : ℕ)
    (hq : 0 < Real.log q) (hL : Real.log q < L) :
    ‖bumpMatrixElement δ q L m n
        - ((1/2) * cosBumpIntegralFull δ q L ((m : ℝ) - n)
            - (1/2) * cosBumpIntegralFull δ q L ((m : ℝ) + n))‖
      ≤ gaussianDecayBound δ q L := by
  rw [bumpMatrixElement_eq_cos]
  -- regroup: (½A − ½B) − (½A' − ½B') = ½(A−A') − ½(B−B')
  have hregroup :
      ((1/2) * cosBumpIntegral δ q L ((m : ℝ) - n)
          - (1/2) * cosBumpIntegral δ q L ((m : ℝ) + n))
        - ((1/2) * cosBumpIntegralFull δ q L ((m : ℝ) - n)
            - (1/2) * cosBumpIntegralFull δ q L ((m : ℝ) + n))
      = (1/2) * (cosBumpIntegral δ q L ((m : ℝ) - n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) - n))
        - (1/2) * (cosBumpIntegral δ q L ((m : ℝ) + n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) + n)) := by ring
  rw [hregroup]
  -- B9 at both frequencies, folded into gaussianDecayBound
  have hMN' : ‖cosBumpIntegral δ q L ((m : ℝ) - n)
                - cosBumpIntegralFull δ q L ((m : ℝ) - n)‖
              ≤ gaussianDecayBound δ q L :=
    cosBumpIntegral_sub_full_norm_le_gaussianDecay δ hδ q L ((m : ℝ) - n) hq hL
  have hPN' : ‖cosBumpIntegral δ q L ((m : ℝ) + n)
                - cosBumpIntegralFull δ q L ((m : ℝ) + n)‖
              ≤ gaussianDecayBound δ q L :=
    cosBumpIntegral_sub_full_norm_le_gaussianDecay δ hδ q L ((m : ℝ) + n) hq hL
  -- ‖½X − ½Y‖ ≤ ‖½X‖ + ‖½Y‖ = ½‖X‖ + ½‖Y‖ ≤ ½·decay + ½·decay = decay+decay
  calc ‖(1/2) * (cosBumpIntegral δ q L ((m : ℝ) - n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) - n))
        - (1/2) * (cosBumpIntegral δ q L ((m : ℝ) + n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) + n))‖
      ≤ ‖(1/2) * (cosBumpIntegral δ q L ((m : ℝ) - n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) - n))‖
        + ‖(1/2) * (cosBumpIntegral δ q L ((m : ℝ) + n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) + n))‖ := norm_sub_le _ _
    _ = (1/2) * ‖cosBumpIntegral δ q L ((m : ℝ) - n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) - n)‖
        + (1/2) * ‖cosBumpIntegral δ q L ((m : ℝ) + n)
                  - cosBumpIntegralFull δ q L ((m : ℝ) + n)‖ := by
        rw [norm_mul, norm_mul, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    _ ≤ (1/2) * gaussianDecayBound δ q L + (1/2) * gaussianDecayBound δ q L := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hMN' (by norm_num)
        · exact mul_le_mul_of_nonneg_left hPN' (by norm_num)
    _ = gaussianDecayBound δ q L := by ring

end RHFormalization
