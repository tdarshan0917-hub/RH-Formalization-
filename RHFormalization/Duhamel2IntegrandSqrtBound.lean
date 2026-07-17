import RHFormalization.Duhamel2IntegrandBound
import RHFormalization.HeatSumSqrtBound

/-!
# Brick 2, Stone 6B': the SHARP order-2 Duhamel integrand bound
`|duhamel2Integrand t u| ≤ B²·(√(π/((t-u)c))/2)·(√(π/(uc))/2)`, c=(π/L)², for
0<u, 0<t-u. Stone 6B with the sharp s^{-1/2} heat bound (stone 7') → integrable
(t-u)^{-1/2}u^{-1/2}, finite Beta convolution. The geometric ~s^{-1} would diverge.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- **Stone 6B' (sharp)**: integrable `B²·√(π/((t-u)c))/2·√(π/(uc))/2` bound. -/
theorem abs_duhamel2Integrand_le_sqrt
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (t u : ℝ) (hu : 0 < u) (htu : 0 < t - u) :
    |duhamel2Integrand (N := N) δ qs w L t u|
      ≤ ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
          * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2)
             * (Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2)) / 2)) := by
  refine le_trans (abs_duhamel2Integrand_le δ hδ qs w L hL t u) ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have h1 : (∑ n : Fin N, |heatWeight L (t - u) n|)
      ≤ Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2 := by
    have habs : ∀ n : Fin N, |heatWeight L (t - u) n| = heatWeight L (t - u) n := by
      intro n; unfold heatWeight; exact abs_of_pos (Real.exp_pos _)
    simp only [habs]; exact sum_heatWeight_le_sqrt L hL (t - u) htu
  have h2 : (∑ m : Fin N, |heatWeight L u m|)
      ≤ Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2)) / 2 := by
    have habs : ∀ m : Fin N, |heatWeight L u m| = heatWeight L u m := by
      intro m; unfold heatWeight; exact abs_of_pos (Real.exp_pos _)
    simp only [habs]; exact sum_heatWeight_le_sqrt L hL u hu
  have hb1_nonneg : 0 ≤ Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2 := by positivity
  exact mul_le_mul h1 h2 (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hb1_nonneg

#print axioms abs_duhamel2Integrand_le_sqrt
end
end RHFormalization
