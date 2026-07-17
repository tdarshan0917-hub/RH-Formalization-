import RHFormalization.Duhamel2Integrand
import RHFormalization.GalerkinDuhamelTraceBound
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
# Order-2 Duhamel integrand bound, correctly scaled

The Galerkin potential matrix carries the density/window prefactor `2 / L`.
Therefore the second-order trace bound carries

  ((2 / L) * ∑ q, |w q| * bumpMass δ q L)^2

not the unscaled `(∑ q, |w q| * bumpMass δ q L)^2`.

This file fixes the previous mismatch against
`abs_trace_galerkinV_diag_le`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- Order-2 integrand bound with the correct `(2/L)` prefactor. -/
theorem abs_duhamel2Integrand_le
    (δ : ℝ) (hδ : 0 < δ)
    (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (t u : ℝ) :
    |duhamel2Integrand (N := N) δ qs w L t u|
      ≤
      ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
        *
        ((∑ n : Fin N, |heatWeight (N := N) L (t - u) n|)
          *
          (∑ m : Fin N, |heatWeight (N := N) L u m|)) := by
  unfold duhamel2Integrand
  exact
    abs_trace_galerkinV_diag_le
      (N := N)
      δ hδ qs w L (le_of_lt hL)
      (heatWeight (N := N) L (t - u))
      (heatWeight (N := N) L u)

/--
Order-2 integrand bound after applying the uniform heat-sum estimates.
-/
theorem abs_duhamel2Integrand_le_heat
    (δ : ℝ) (hδ : 0 < δ)
    (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (t u : ℝ) (hu : 0 < u) (htu : 0 < t - u) :
    |duhamel2Integrand (N := N) δ qs w L t u|
      ≤
      ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
        *
        ((1 - Real.exp (-((t - u) * (Real.pi / L) ^ 2)))⁻¹
          *
          (1 - Real.exp (-(u * (Real.pi / L) ^ 2)))⁻¹) := by
  have hbase :=
    abs_duhamel2Integrand_le
      (N := N) δ hδ qs w L hL t u

  have hd1 :
      ∑ n : Fin N, |heatWeight (N := N) L (t - u) n|
        ≤ (1 - Real.exp (-((t - u) * (Real.pi / L) ^ 2)))⁻¹ := by
    have habs :
        ∀ n : Fin N,
          |heatWeight (N := N) L (t - u) n|
            = heatWeight (N := N) L (t - u) n := by
      intro n
      unfold heatWeight
      exact abs_of_pos (Real.exp_pos _)
    simp only [habs]
    exact sum_heatWeight_le (N := N) L hL (t - u) htu

  have hd2 :
      ∑ m : Fin N, |heatWeight (N := N) L u m|
        ≤ (1 - Real.exp (-(u * (Real.pi / L) ^ 2)))⁻¹ := by
    have habs :
        ∀ m : Fin N,
          |heatWeight (N := N) L u m|
            = heatWeight (N := N) L u m := by
      intro m
      unfold heatWeight
      exact abs_of_pos (Real.exp_pos _)
    simp only [habs]
    exact sum_heatWeight_le (N := N) L hL u hu

  have hsum2_nonneg :
      0 ≤ ∑ m : Fin N, |heatWeight (N := N) L u m| := by
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

  have hbound1_nonneg :
      0 ≤ (1 - Real.exp (-((t - u) * (Real.pi / L) ^ 2)))⁻¹ := by
    apply inv_nonneg.mpr
    have hlt : Real.exp (-((t - u) * (Real.pi / L) ^ 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have hpos : 0 < (t - u) * (Real.pi / L) ^ 2 := by positivity
      linarith
    linarith

  have hprod :
      (∑ n : Fin N, |heatWeight (N := N) L (t - u) n|)
          *
          (∑ m : Fin N, |heatWeight (N := N) L u m|)
        ≤
        (1 - Real.exp (-((t - u) * (Real.pi / L) ^ 2)))⁻¹
          *
          (1 - Real.exp (-(u * (Real.pi / L) ^ 2)))⁻¹ := by
    exact mul_le_mul hd1 hd2 hsum2_nonneg hbound1_nonneg

  refine le_trans hbase ?_
  exact mul_le_mul_of_nonneg_left
    hprod
    (sq_nonneg ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L))

#print axioms abs_duhamel2Integrand_le
#print axioms abs_duhamel2Integrand_le_heat

end

end RHFormalization
