import RHFormalization.Duhamel2Integrand
import RHFormalization.PrimePotentialBumpSplit
import Mathlib

/-!
# Galerkin first-order Duhamel term

This is the missing order-1 object for the genuine position-space operator.

Compass:
* `galerkinK` = free diagonal Laplacian matrix.
* `galerkinV` = genuine off-diagonal bump potential matrix.
* This is NOT the diagonal toy `primePotential`.

The target after this file:
  order-1 Duhamel term = B-side Gaussian spike package.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/--
First-order Galerkin Duhamel integrand:
  Tr(e^{-(t-u)K} V e^{-uK})

Since K is diagonal, this is the object whose diagonal/spike extraction should
produce the B-side Gaussian spike package.
-/
noncomputable def duhamel1Integrand
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) : ℝ :=
  (Matrix.diagonal (heatWeight (N := N) L (t - u))
    * galerkinV (N := N) δ qs w L
    * Matrix.diagonal (heatWeight (N := N) L u)).trace

#check duhamel1Integrand
#check galerkinV
#check VmatrixElement_eq_sum_bumps
#check heatWeight
#check duhamel2Integrand

#print axioms duhamel1Integrand

end
end RHFormalization
