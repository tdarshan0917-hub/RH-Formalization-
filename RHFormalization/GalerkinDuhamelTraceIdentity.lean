import RHFormalization.GalerkinDuhamelIdentity
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

/-- `Tr(e^{-t(K+V)}) = Tr(e^{-tK}) + ∫₀ᵗ Tr(sandwich) du`.
The trace-level Dyson expansion. -/
theorem galerkinDuhamel_trace_identity
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
      = (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
        + ∫ u in (0:ℝ)..t,
            (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (u • (-(galerkinK (N := N) L
                  + galerkinV (N := N) δ qs w L)))).trace := by
  have hid := galerkinDuhamel_identity (N := N) δ qs w L t
  have htr := congrArg Matrix.trace hid
  rw [Matrix.trace_sub] at htr
  -- trace of the integral = integral of the trace (real version)
  set F : ℝ → Matrix (Fin N) (Fin N) ℝ :=
    fun u => NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
      * (-(galerkinV (N := N) δ qs w L))
      * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))) with hF
  have hcomm : (∫ u in (0:ℝ)..t, F u).trace = ∫ u in (0:ℝ)..t, (F u).trace := by
    rw [trace_integral_comm_real (N := N) t F (by rw [hF]; fun_prop)]
  -- htr : Tr(E(t)) - Tr(D(t)) = Tr(∫ F)
  -- rearrange to Tr(E(t)) = Tr(D(t)) + Tr(∫ F), then commute
  rw [hcomm] at htr
  linear_combination htr

#print axioms galerkinDuhamel_trace_identity

end

end RHFormalization
