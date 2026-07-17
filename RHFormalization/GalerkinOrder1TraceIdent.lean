import RHFormalization.GalerkinSandwichSplit
import RHFormalization.GalerkinFreeHeatDiagonal
import RHFormalization.GalerkinDuhamel1Term
import Mathlib

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Matrix
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **Order-1 free-free trace = -duhamel1Integrand.** -/
theorem galerkinOrder1FreeFree_trace_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L)))).trace
      = - duhamel1Integrand (N := N) δ qs w L t u := by
  rw [galerkinFreeHeat_eq_diagonal, galerkinFreeHeat_eq_diagonal]
  unfold duhamel1Integrand
  first
    | rw [mul_neg, Matrix.trace_neg, neg_inj]
    | (rw [show -((Matrix.diagonal fun m => heatWeight (N := N) L (t - u) m)
            * galerkinV (N := N) δ qs w L)
          * (Matrix.diagonal fun m => heatWeight (N := N) L u m)
        = -((Matrix.diagonal fun m => heatWeight (N := N) L (t - u) m)
            * galerkinV (N := N) δ qs w L
            * (Matrix.diagonal fun m => heatWeight (N := N) L u m)) from by
          rw [Matrix.neg_mul, Matrix.mul_assoc]]
       rw [mul_neg, Matrix.trace_neg, neg_inj])
    | (rw [Matrix.neg_mul]; rw [mul_neg, Matrix.trace_neg, neg_inj])
    | (simp only [Matrix.neg_mul, Matrix.mul_assoc]; rw [mul_neg, Matrix.trace_neg, neg_inj])

#print axioms galerkinOrder1FreeFree_trace_eq
