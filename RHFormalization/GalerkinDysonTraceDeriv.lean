import RHFormalization.GalerkinDysonInterpFullDeriv
import RHFormalization.GalerkinDysonInterp
import Mathlib

/-!
# Trace of the Dyson interpolation derivative.

`d/du Tr(dysonInterp) = Tr(d/du dysonInterp)`, since trace is linear and (on the
finite-dim matrix space) continuous. The banked `hasDerivAt_dysonInterp` gives
the matrix derivative; trace-as-CLM transports it.
-/

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

/-- Trace as a continuous linear map (finite-dim ⇒ continuous). -/
noncomputable def traceCLM : Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin N) ℝ ℝ).toContinuousLinearMap

/-- **Trace of the interpolation derivative.** -/
theorem hasDerivAt_trace_dysonInterp
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => (dysonInterp (N := N) δ qs w L t v).trace)
      ((NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L))) * (galerkinK (N := N) L)
          * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
        + NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
             * (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace) u := by
  have hderiv := hasDerivAt_dysonInterp (N := N) δ qs w L t u
  exact (traceCLM (N := N)).hasFDerivAt.comp_hasDerivAt u hderiv

#print axioms hasDerivAt_trace_dysonInterp
