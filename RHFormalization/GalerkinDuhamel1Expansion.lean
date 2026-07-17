import RHFormalization.GalerkinDuhamel1Term
import Mathlib

/-!
# Galerkin first-order Duhamel expansion

Expands the new order-1 Duhamel integrand into its diagonal trace sum.

Compass:
* genuine operator side: `galerkinV`
* free heat factors: diagonal `heatWeight`
* not the diagonal toy `primePotential`
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/--
Trace expansion for the first-order Galerkin Duhamel integrand.

This is the first algebraic step toward the spike-identification:
the order-1 trace only sees the diagonal matrix elements `galerkinV m m`,
which then expand into the bump/spike contributions.
-/
theorem duhamel1Integrand_eq_diag_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u =
      ∑ m : Fin N,
        heatWeight (N := N) L (t - u) m
          * galerkinV (N := N) δ qs w L m m
          * heatWeight (N := N) L u m := by
  unfold duhamel1Integrand
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

#print axioms duhamel1Integrand_eq_diag_sum

end
end RHFormalization
