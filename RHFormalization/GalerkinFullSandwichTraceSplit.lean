import RHFormalization.GalerkinFullToDiagonalDuhamelSplit
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

/-- **Trace of the full-semigroup split.** Taking trace of `galerkinFullSandwich_split`
(trace is additive): the trace of the full integrand = trace of the diagonal
order-1 term + trace of the quadratic remainder. This is the trace-level split
the uniform bound attaches to. -/
theorem galerkinFullSandwich_trace_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))).trace
      = (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp (u • (-(galerkinK (N := N) L)))).trace
        + (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
            * (-(galerkinV (N := N) δ qs w L))
            * (∫ s in (0:ℝ)..u,
                NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
                  * (-(galerkinV (N := N) δ qs w L))
                  * NormedSpace.exp (s • (-(galerkinK (N := N) L
                      + galerkinV (N := N) δ qs w L))))).trace := by
  rw [galerkinFullSandwich_split (N := N) δ qs w L t u, Matrix.trace_add]

#print axioms galerkinFullSandwich_trace_split
end
end RHFormalization
