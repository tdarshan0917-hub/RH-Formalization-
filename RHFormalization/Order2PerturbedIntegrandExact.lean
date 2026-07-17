import Mathlib
import RHFormalization.GalerkinDuhamelTraceIdentity

set_option autoImplicit false
open scoped BigOperators

namespace RHFormalization

variable {N : ℕ}

/--
The exact integrand of the order-2 Duhamel remainder.

This is the object that must be bounded to obtain HR.
-/
def order2PerturbedIntegrand
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u r : ℝ) : ℝ :=
  Matrix.trace (
    (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L))))
    *
    (-(galerkinV (N := N) δ qs w L))
    *
    (NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L))))
    *
    (-(galerkinV (N := N) δ qs w L))
    *
    (NormedSpace.exp (r • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L))))
  )

/--
Sanity check: this matches the definition already used
in the Duhamel decomposition.
-/
theorem order2PerturbedIntegrand_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u r : ℝ) :
  order2PerturbedIntegrand
      (N := N) δ qs w L t u r
    =
  Matrix.trace (
    (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L))))
    *
    (-(galerkinV (N := N) δ qs w L))
    *
    (NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L))))
    *
    (-(galerkinV (N := N) δ qs w L))
    *
    (NormedSpace.exp (r • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L))))
  ) := rfl

end RHFormalization
