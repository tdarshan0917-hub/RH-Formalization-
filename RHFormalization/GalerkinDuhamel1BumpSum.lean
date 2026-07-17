import RHFormalization.GalerkinDuhamel1Expansion
import Mathlib

/-!
# Galerkin first-order Duhamel bump expansion

This expands the first-order Galerkin Duhamel term from the diagonal trace sum
into the bump/spike contributions using `VmatrixElement_eq_sum_bumps`.

Compass:
* genuine operator: `galerkinV`
* first-order Duhamel term: `duhamel1Integrand`
* next target after this: identify this bump sum with the B-side spike package.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

theorem duhamel1Integrand_eq_bump_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u =
      ∑ m : Fin N,
        heatWeight (N := N) L (t - u) m
          * ((2 / L) * ∑ q ∈ qs,
                w q * bumpMatrixElement δ q L (m + 1) (m + 1))
          * heatWeight (N := N) L u m := by
  rw [duhamel1Integrand_eq_diag_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [galerkinV_apply]
  rw [VmatrixElement_eq_sum_bumps]

#print axioms duhamel1Integrand_eq_bump_sum

end
end RHFormalization
