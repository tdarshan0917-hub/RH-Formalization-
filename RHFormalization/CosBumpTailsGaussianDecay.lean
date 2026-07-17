import RHFormalization.CosBumpLeftTailCosDrop
import RHFormalization.CosBumpRightTailCosDrop
import RHFormalization.GaussianIicTail
import RHFormalization.GaussianIoiTail
set_option autoImplicit false
open MeasureTheory Real Set

namespace RHFormalization

/-- Constant-pull for a Gaussian tail on `Iic (-R)`:
`∫ gaussBump = (1/√(2πδ²)) · ∫ exp(-(1/(2δ²))·u²)`. -/
theorem gaussBump_Iic_eq_const_mul (δ R : ℝ) :
    ∫ u in Iic (-R), gaussBump δ u
      = (1 / Real.sqrt (2*Real.pi*δ^2))
        * ∫ u in Iic (-R), Real.exp (-(1/(2*δ^2)) * u^2) := by
  have hpt : (fun u => gaussBump δ u)
      = (fun u => (1 / Real.sqrt (2*Real.pi*δ^2)) * Real.exp (-(1/(2*δ^2)) * u^2)) := by
    funext u; unfold gaussBump; rw [neg_div]; ring_nf
  rw [show (∫ u in Iic (-R), gaussBump δ u)
        = ∫ u in Iic (-R), (1 / Real.sqrt (2*Real.pi*δ^2))
            * Real.exp (-(1/(2*δ^2)) * u^2) from by rw [hpt]]
  rw [integral_const_mul]

/-- Constant-pull for a Gaussian tail on `Ioi R`. -/
theorem gaussBump_Ioi_eq_const_mul (δ R : ℝ) :
    ∫ u in Ioi R, gaussBump δ u
      = (1 / Real.sqrt (2*Real.pi*δ^2))
        * ∫ u in Ioi R, Real.exp (-(1/(2*δ^2)) * u^2) := by
  have hpt : (fun u => gaussBump δ u)
      = (fun u => (1 / Real.sqrt (2*Real.pi*δ^2)) * Real.exp (-(1/(2*δ^2)) * u^2)) := by
    funext u; unfold gaussBump; rw [neg_div]; ring_nf
  rw [show (∫ u in Ioi R, gaussBump δ u)
        = ∫ u in Ioi R, (1 / Real.sqrt (2*Real.pi*δ^2))
            * Real.exp (-(1/(2*δ^2)) * u^2) from by rw [hpt]]
  rw [integral_const_mul]

/-- Explicit Gaussian-decay bound on the sum of the two cos-bump tails.
For `q` with `0 < log q` (i.e. `q ≥ 2`) and `log q < L`, both tails decay:
each is bounded by a `(const)·exp(-R²/(2δ²))/(R/(2δ²))` quantity with
`R = log q` (left) and `R = L - log q` (right). -/
theorem cosBumpTails_norm_le_gaussianDecay
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (j : ℝ)
    (hq : 0 < Real.log q) (hL : Real.log q < L) :
    ‖cosBumpLeftTail δ q L j‖ + ‖cosBumpRightTail δ q L j‖
      ≤ (1 / Real.sqrt (2*Real.pi*δ^2))
          * (Real.exp (-(1/(2*δ^2) * (Real.log q)^2))
              / ((1/(2*δ^2)) * Real.log q))
        + (1 / Real.sqrt (2*Real.pi*δ^2))
          * (Real.exp (-(1/(2*δ^2) * (L - Real.log q)^2))
              / ((1/(2*δ^2)) * (L - Real.log q))) := by
  have hb : (0:ℝ) < 1/(2*δ^2) := by positivity
  have hconst : (0:ℝ) ≤ 1 / Real.sqrt (2*Real.pi*δ^2) := by positivity
  -- LEFT: cos-drop → const-pull → 8a
  have hleft : ‖cosBumpLeftTail δ q L j‖
      ≤ (1 / Real.sqrt (2*Real.pi*δ^2))
          * (Real.exp (-(1/(2*δ^2) * (Real.log q)^2))
              / ((1/(2*δ^2)) * Real.log q)) := by
    refine le_trans (norm_cosBumpLeftTail_le_gaussBump_tail δ hδ q L j) ?_
    rw [show (0 - Real.log q) = -(Real.log q) by ring,
        gaussBump_Iic_eq_const_mul δ (Real.log q)]
    exact mul_le_mul_of_nonneg_left
      (gaussian_Iic_tail_le (1/(2*δ^2)) (Real.log q) hb hq) hconst
  -- RIGHT: cos-drop → const-pull → 8b
  have hright : ‖cosBumpRightTail δ q L j‖
      ≤ (1 / Real.sqrt (2*Real.pi*δ^2))
          * (Real.exp (-(1/(2*δ^2) * (L - Real.log q)^2))
              / ((1/(2*δ^2)) * (L - Real.log q))) := by
    have hRpos : (0:ℝ) < L - Real.log q := by linarith
    refine le_trans (norm_cosBumpRightTail_le_gaussBump_tail δ hδ q L j) ?_
    rw [gaussBump_Ioi_eq_const_mul δ (L - Real.log q)]
    exact mul_le_mul_of_nonneg_left
      (gaussian_Ioi_tail_le (1/(2*δ^2)) (L - Real.log q) hb hRpos) hconst
  linarith [hleft, hright]

end RHFormalization
