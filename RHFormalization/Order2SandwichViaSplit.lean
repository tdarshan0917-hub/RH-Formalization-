import RHFormalization.GalerkinSandwichSplit
import RHFormalization.DBFFO1SandwichTraceDecomposition
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The order-2 sandwich trace as the trace of its defining matrix. -/
theorem galerkinOrder2SandwichTrace_eq_split_trace
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    galerkinOrder2SandwichTrace (N := N) δ qs w L t u
      = (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * (∫ r in (0:ℝ)..u,
              NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
                * (-(galerkinV (N := N) δ qs w L))
                * NormedSpace.exp (r • (-(galerkinK (N := N) L
                    + galerkinV (N := N) δ qs w L))))).trace := by
  rfl

#print axioms galerkinOrder2SandwichTrace_eq_split_trace

end

end RHFormalization
