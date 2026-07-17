import RHFormalization.Order2PointwiseSplit
import RHFormalization.GalerkinFreeHeatDiagonal
import RHFormalization.HeatWeightAdditive
import RHFormalization.Duhamel2Integrand
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

/--
Cyclically move the first free heat factor to the end and fuse it with
the final free heat factor.

This is consumed by
`galerkinOrder2Pointwise_free_eq_duhamel2Integrand`.
-/
theorem order2Free_trace_cyclic_fusion
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u r : ℝ) :
    ((Matrix.diagonal (heatWeight (N := N) L (t - u)))
        * (-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L (u - r)))
        * (-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L r))).trace
      =
    ((-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal (heatWeight (N := N) L (u - r)))
        * (-(galerkinV (N := N) δ qs w L))
        * (Matrix.diagonal
            (heatWeight (N := N) L (r + (t - u))))).trace := by
  set D1 :=
    Matrix.diagonal (heatWeight (N := N) L (t - u))
      with hD1
  set Vn :=
    -(galerkinV (N := N) δ qs w L)
      with hVn
  set D2 :=
    Matrix.diagonal (heatWeight (N := N) L (u - r))
      with hD2
  set D3 :=
    Matrix.diagonal (heatWeight (N := N) L r)
      with hD3

  have hassoc :
      D1 * Vn * D2 * Vn * D3
        = D1 * (Vn * D2 * Vn * D3) := by
    simp only [mul_assoc]

  rw [hassoc]

  -- Tr(D1 · X) = Tr(X · D1)
  rw [Matrix.trace_mul_comm D1 (Vn * D2 * Vn * D3)]

  have hassoc2 :
      Vn * D2 * Vn * D3 * D1
        = Vn * D2 * Vn * (D3 * D1) := by
    simp only [mul_assoc]

  rw [hassoc2]

  -- D(r) · D(t-u) = D(r + (t-u)).
  rw [hD3, hD1, diagonal_heatWeight_mul L r (t - u)]

/--
The all-free summand produced by `galerkinOrder2Pointwise_split` is exactly
the banked order-2 integrand evaluated at the shifted simplex variable
`r + (t-u)`.

Indeed:
`t - (r + (t-u)) = u-r`.
-/
theorem galerkinOrder2Pointwise_free_eq_duhamel2Integrand
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u r : ℝ) :
    (NormedSpace.exp
          ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          ((u - r) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (r • (-(galerkinK (N := N) L)))).trace
      =
    duhamel2Integrand
      (N := N) δ qs w L t (r + (t - u)) := by

  -- Convert all three free semigroups into diagonal heat matrices.
  rw [galerkinFreeHeat_eq_diagonal,
      galerkinFreeHeat_eq_diagonal,
      galerkinFreeHeat_eq_diagonal]

  -- Cyclicity plus the free semigroup law.
  rw [order2Free_trace_cyclic_fusion]

  unfold duhamel2Integrand

  have htime :
      t - (r + (t - u)) = u - r := by
    ring

  rw [htime]

  -- The two perturbation minus signs cancel.
  simp only [neg_mul, mul_neg, neg_neg]

#print axioms order2Free_trace_cyclic_fusion
#print axioms galerkinOrder2Pointwise_free_eq_duhamel2Integrand

end

end RHFormalization
