import RHFormalization.Order2PointwiseFreeIdent
import RHFormalization.Duhamel2IntegrandSqrtBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/--
The all-free pointwise summand from the second Duhamel split inherits
the banked square-root estimate after the shifted-time identification.

This theorem is consumed by the free-part interval-integral estimate.
-/
theorem abs_galerkinOrder2Pointwise_free_le_sqrt
    (δ : ℝ) (hδ : 0 < δ)
    (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (hL : 0 < L)
    (t u r : ℝ)
    (hr0 : 0 ≤ r)
    (hru : r < u)
    (hut : u < t) :
    |(
      NormedSpace.exp
          ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          ((u - r) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (r • (-(galerkinK (N := N) L)))
    ).trace|
      ≤
    ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
      *
      ((Real.sqrt
          (Real.pi /
            ((t - (r + (t - u))) * (Real.pi / L) ^ 2)) / 2)
        *
       (Real.sqrt
          (Real.pi /
            ((r + (t - u)) * (Real.pi / L) ^ 2)) / 2)) := by

  rw [galerkinOrder2Pointwise_free_eq_duhamel2Integrand]

  exact abs_duhamel2Integrand_le_sqrt
    (N := N)
    δ hδ qs w L hL
    t (r + (t - u))
    (by linarith)
    (by linarith)

#print axioms abs_galerkinOrder2Pointwise_free_le_sqrt

end

end RHFormalization
