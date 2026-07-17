import RHFormalization.HeatWeightAdditive
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The leading all-diagonal sandwich trace equals the banked-bound shape. -/
theorem leadingDiagSandwich_trace_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u r : ℝ) :
    ((Matrix.diagonal (heatWeight (N := N) L (t - u)))
        * (-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L (u - r)))
        * (-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L r))).trace
      = ((-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L (u - r)))
        * (-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L (r + (t - u))))).trace := by
  set D1 := Matrix.diagonal (heatWeight (N := N) L (t - u)) with hD1
  set V := -(galerkinV (N := N) δ qs w L) with hV
  set D2 := Matrix.diagonal (heatWeight (N := N) L (u - r)) with hD2
  set D3 := Matrix.diagonal (heatWeight (N := N) L r) with hD3
  -- re-associate LHS product as D1 * (V * D2 * V * D3)
  have hassoc : D1 * V * D2 * V * D3 = D1 * (V * D2 * V * D3) := by
    simp only [mul_assoc]
  rw [hassoc]
  -- cyclic trace: Tr(D1 * X) = Tr(X * D1)
  rw [Matrix.trace_mul_comm D1 (V * D2 * V * D3)]
  -- now goal LHS is Tr((V * D2 * V * D3) * D1); re-associate to expose D3 * D1
  have hassoc2 : V * D2 * V * D3 * D1 = V * D2 * V * (D3 * D1) := by
    simp only [mul_assoc]
  rw [hassoc2]
  -- fuse D3 * D1 = diagonal(heatWeight L (r + (t-u)))
  rw [hD3, hD1, diagonal_heatWeight_mul L r (t - u)]

#print axioms leadingDiagSandwich_trace_eq

end

end RHFormalization
