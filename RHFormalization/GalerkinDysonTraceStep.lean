import RHFormalization.GalerkinDuhamelIdentity
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

/-- **Dyson trace identity.** Trace of the banked order-1 Duhamel identity:
`Tr(LHS) = Tr(free heat) + Tr(∫ sandwich)`. The trace of the sandwich integral
is left as `Tr(∫...)`; commuting it with the integral is a separate step. This
brick just transports the banked operator identity to the trace level. -/
theorem galerkinDuhamel_trace_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
      - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
      = (∫ u in (0:ℝ)..t,
          NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (u • (-(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L)))).trace := by
  have hid := galerkinDuhamel_identity (N := N) δ qs w L t
  rw [← Matrix.trace_sub, hid]

#print axioms galerkinDuhamel_trace_eq

end
end RHFormalization
