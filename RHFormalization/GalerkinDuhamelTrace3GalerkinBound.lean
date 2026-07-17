import RHFormalization.GalerkinDuhamelTrace3Bound
import RHFormalization.VMatrixElementBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/--
Galerkin specialization of the abstract order-3 all-free trace bound.

This is a fixed-order helper only. It does not control the complete
perturbed-semigroup tail.
-/
theorem abs_trace_neg_galerkinV_diag3_le
    (δ : ℝ) (hδ : 0 < δ)
    (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (hL : 0 < L)
    (d₁ d₂ d₃ : Fin N → ℝ) :
    |(
      (-(galerkinV (N := N) δ qs w L))
        * Matrix.diagonal d₁
        * (-(galerkinV (N := N) δ qs w L))
        * Matrix.diagonal d₂
        * (-(galerkinV (N := N) δ qs w L))
        * Matrix.diagonal d₃
    ).trace|
      ≤
    ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 3
      *
    ((∑ j, |d₁ j|)
      * (∑ k, |d₂ k|)
      * (∑ i, |d₃ i|)) := by

  have hmass :
      0 ≤ ∑ q ∈ qs, |w q| * bumpMass δ q L := by
    apply Finset.sum_nonneg
    intro q _
    apply mul_nonneg (abs_nonneg _)

    unfold bumpMass
    apply intervalIntegral.integral_nonneg hL.le

    intro x _
    exact le_of_lt
      (gaussBump_pos δ hδ (x - Real.log (q : ℝ)))

  have h2L : 0 ≤ 2 / L := by
    positivity

  refine
    abs_trace_V_diag_V_diag_V_diag_le
      (N := N)
      (V := -(galerkinV (N := N) δ qs w L))
      (d₁ := d₁)
      (d₂ := d₂)
      (d₃ := d₃)
      (B :=
        (2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L)
      ?_ ?_

  · exact mul_nonneg h2L hmass

  · intro i j

    have hentry :
        |galerkinV (N := N) δ qs w L i j|
          ≤
        (2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L := by

      rw [galerkinV_apply, abs_mul, abs_of_nonneg h2L]

      exact
        mul_le_mul_of_nonneg_left
          (abs_VmatrixElement_le
            δ hδ qs w L hL.le
            (i + 1) (j + 1))
          h2L

    change
      |-(galerkinV (N := N) δ qs w L i j)|
        ≤
      (2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L

    simpa only [abs_neg] using hentry

#print axioms abs_trace_neg_galerkinV_diag3_le

end

end RHFormalization
