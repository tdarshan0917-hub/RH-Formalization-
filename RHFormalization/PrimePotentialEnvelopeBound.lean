import RHFormalization.PrimePotentialPosition
import RHFormalization.SupVBound
set_option autoImplicit false
open Finset Real

namespace RHFormalization

/-- Peak bound for a general-δ Gaussian bump: `gaussBump δ y ≤ 1/√(2πδ²)`.
The Gaussian is maximized at its center, where the exponential is 1. -/
theorem gaussBump_le_peak_delta (δ : ℝ) (hδ : 0 < δ) (y : ℝ) :
    gaussBump δ y ≤ 1 / Real.sqrt (2 * Real.pi * δ ^ 2) := by
  unfold gaussBump
  rw [div_le_div_iff_of_pos_right (by positivity)]
  have hexp : Real.exp (-y ^ 2 / (2 * δ ^ 2)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg y]
    · positivity
  linarith [hexp]

/-- **A.ENV-DOM, envelope rung.** The prime potential `V_R(x) = ∑_q w(q)·gaussBump δ (x−log q)`
is bounded pointwise by the weighted count of active primes times the Gaussian peak:
`|V_R(x)| ≤ (∑_q |w q|) · (1/√(2πδ²))`, uniformly in `x`. This is the crude confining
envelope; the manuscript's `V_R^# ≤ θ·V_env` refines it, but this is the load-bearing
"bumps don't blow up" bound that the KLMN form control rests on. -/
theorem primePotentialFn_abs_le_weighted_peak
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) :
    |primePotentialFn δ qs w x|
      ≤ (∑ q ∈ qs, |w q|) * (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) := by
  unfold primePotentialFn
  calc |∑ q ∈ qs, w q * gaussBump δ (x - Real.log q)|
      ≤ ∑ q ∈ qs, |w q * gaussBump δ (x - Real.log q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ qs, |w q| * (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul, abs_of_pos (gaussBump_pos δ hδ _)]
        exact mul_le_mul_of_nonneg_left
          (gaussBump_le_peak_delta δ hδ _) (abs_nonneg _)
    _ = (∑ q ∈ qs, |w q|) * (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) := by
        rw [← Finset.sum_mul]

#print axioms gaussBump_le_peak_delta
#print axioms primePotentialFn_abs_le_weighted_peak

end RHFormalization
