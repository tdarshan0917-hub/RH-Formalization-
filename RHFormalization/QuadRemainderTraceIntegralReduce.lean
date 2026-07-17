import RHFormalization.GalerkinFullSandwichTraceSplit
import RHFormalization.DKeyFormTraceAssembly
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

/-- Mechanical quadratic-remainder reduction: trace-of-integral ≤ integral-of-absolute-trace.
    `0 ≤ u` needed because interval integrals are oriented. -/
theorem quadRemainder_trace_le_integral_abs
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t u : ℝ) (hu : 0 ≤ u) :
    |((Matrix.diagonal fun m => heatWeight L (t - u) m)
        * (-(galerkinV (N := N) δ qs w L))
        * ∫ s in (0 : ℝ)..u,
            NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (s • -(galerkinK (N := N) L
                  + galerkinV (N := N) δ qs w L))).trace|
      ≤ ∫ s in (0 : ℝ)..u,
          |((Matrix.diagonal fun m => heatWeight L (t - u) m)
            * (-(galerkinV (N := N) δ qs w L))
            * (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
                * (-(galerkinV (N := N) δ qs w L))
                * NormedSpace.exp (s • -(galerkinK (N := N) L
                    + galerkinV (N := N) δ qs w L)))).trace| := by
  set D : Matrix (Fin N) (Fin N) ℝ :=
    (Matrix.diagonal fun m => heatWeight L (t - u) m) * (-(galerkinV (N := N) δ qs w L)) with hD
  set F : ℝ → Matrix (Fin N) (Fin N) ℝ :=
    fun s => NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (s • -(galerkinK (N := N) L
                  + galerkinV (N := N) δ qs w L)) with hF
  have hcont : Continuous (fun s : ℝ => D * F s) := by
    rw [hD, hF]; fun_prop
  have hcontF : Continuous F := by rw [hF]; fun_prop
  have hint : IntervalIntegrable F volume 0 u := hcontF.intervalIntegrable 0 u
  -- left-multiplication by D is a continuous linear map; it commutes with ∫
  have hstep1 : D * (∫ s in (0:ℝ)..u, F s) = ∫ s in (0:ℝ)..u, D * F s := by
    have h := (ContinuousLinearMap.intervalIntegral_comp_comm
      ((LinearMap.mulLeft ℝ D).toContinuousLinearMap) hint)
    simpa [LinearMap.mulLeft_apply] using h.symm
  rw [hstep1]
  rw [trace_integral_comm_real (N := N) u (fun s : ℝ => D * F s) hcont]
  exact intervalIntegral.abs_integral_le_integral_abs hu

#print axioms quadRemainder_trace_le_integral_abs

end

end RHFormalization
