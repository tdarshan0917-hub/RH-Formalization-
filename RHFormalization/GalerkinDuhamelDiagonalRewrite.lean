import RHFormalization.GalerkinDuhamelDiagonalBridge
import Mathlib

namespace RHFormalization

open scoped BigOperators

/--
Order-1 Duhamel integrand written using the clean diagonal free-heat matrix.
This replaces the failed Matrix.exp free-heat object.
-/
theorem duhamel1Integrand_eq_trace_freeHeatDiagonal
    {N : ℕ} (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u
      =
    (galerkinFreeHeatDiagonal (N := N) L (t - u)
      * galerkinV δ qs w L
      * galerkinFreeHeatDiagonal (N := N) L u).trace := by
  rfl

/--
Order-2 Duhamel integrand written using the clean diagonal free-heat matrix.
-/
theorem duhamel2Integrand_eq_trace_freeHeatDiagonal
    {N : ℕ} (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t u : ℝ) :
    duhamel2Integrand (N := N) δ qs w L t u
      =
    (galerkinV δ qs w L
      * galerkinFreeHeatDiagonal (N := N) L (t - u)
      * galerkinV δ qs w L
      * galerkinFreeHeatDiagonal (N := N) L u).trace := by
  rfl

#print axioms duhamel1Integrand_eq_trace_freeHeatDiagonal
#print axioms duhamel2Integrand_eq_trace_freeHeatDiagonal

end RHFormalization
