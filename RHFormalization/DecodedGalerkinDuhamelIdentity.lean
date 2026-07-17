-- SENTINEL: decoded-galerkin-duhamel-v1
import RHFormalization.GalerkinDuhamelIdentityGeneric
import RHFormalization.PrimePotentialDecodedCenter
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Duhamel identity for the manuscript-faithful decoded-center potential. -/
theorem decodedGalerkinDuhamel_identity
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t : ℝ) :
    NormedSpace.exp
        (t • (-(galerkinK (N := N) L
          + decodedGalerkinV (N := N) δ qs w L)))
      - NormedSpace.exp
        (t • (-(galerkinK (N := N) L)))
      =
    ∫ u in (0 : ℝ)..t,
      NormedSpace.exp
          ((t - u) • (-(galerkinK (N := N) L)))
        * (-(decodedGalerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L
            + decodedGalerkinV (N := N) δ qs w L))) := by
  exact
    galerkinDuhamel_identity_of_matrix
      (N := N)
      L
      (decodedGalerkinV (N := N) δ qs w L)
      t

#print axioms decodedGalerkinDuhamel_identity

end

end RHFormalization
