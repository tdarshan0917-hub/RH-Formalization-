import RHFormalization.GalerkinFullSandwichTraceSplit
import RHFormalization.GalerkinFreeHeatDiagonal
import RHFormalization.GalerkinDuhamel1Term
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFormalization
noncomputable section
open Matrix MeasureTheory intervalIntegral
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **First split term = −duhamel1Integrand.** The diagonal order-1 term
`Tr(D(t-u)·(-V)·D_exp(u))` equals `−duhamel1Integrand` after diagonalizing the
free-heat factor and pulling out the sign. Lands the first split term onto the
banked order-1 spike/error machinery. -/
theorem galerkinFirstSplitTerm_eq_neg_duhamel1
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L)))).trace
      = - duhamel1Integrand (N := N) δ qs w L t u := by
  rw [galerkinFreeHeat_eq_diagonal (N := N) L u]
  unfold duhamel1Integrand
  rw [mul_neg, neg_mul, Matrix.trace_neg]

#print axioms galerkinFirstSplitTerm_eq_neg_duhamel1
end
end RHFormalization
