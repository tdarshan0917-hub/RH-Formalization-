import RHFormalization.CosBumpIntegralTailSplit
import RHFormalization.CosBumpTailsGaussianDecay
set_option autoImplicit false
open MeasureTheory Real Set

namespace RHFormalization

/-- **B9 — error-bounded closed form.** The finite cos-bump transform
`cosBumpIntegral` differs from the closed-form full-line transform
`cosBumpIntegralFull` by at most the explicit vanishing Gaussian-tail
quantity from `cosBumpTails_norm_le_gaussianDecay`. -/
theorem cosBumpIntegral_sub_full_norm_le_gaussianDecay
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (j : ℝ)
    (hq : 0 < Real.log q) (hL : Real.log q < L) :
    ‖cosBumpIntegral δ q L j - cosBumpIntegralFull δ q L j‖
      ≤ (1 / Real.sqrt (2*Real.pi*δ^2))
          * (Real.exp (-(1/(2*δ^2) * (Real.log q)^2))
              / ((1/(2*δ^2)) * Real.log q))
        + (1 / Real.sqrt (2*Real.pi*δ^2))
          * (Real.exp (-(1/(2*δ^2) * (L - Real.log q)^2))
              / ((1/(2*δ^2)) * (L - Real.log q))) := by
  have hL0 : (0:ℝ) ≤ L := le_of_lt (lt_trans hq hL)
  -- cosBumpIntegral - Full = -(leftTail + rightTail)
  have hsplit := cosBumpIntegral_eq_full_sub_tails δ hδ q L hL0 j
  have heq : cosBumpIntegral δ q L j - cosBumpIntegralFull δ q L j
      = -(cosBumpLeftTail δ q L j + cosBumpRightTail δ q L j) := by
    rw [hsplit]; ring
  rw [heq, norm_neg]
  -- ‖leftTail + rightTail‖ ≤ ‖leftTail‖ + ‖rightTail‖ ≤ decay
  refine le_trans (norm_add_le _ _) ?_
  exact cosBumpTails_norm_le_gaussianDecay δ hδ q L j hq hL

end RHFormalization
