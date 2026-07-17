import RHFormalization.DecodedGalerkinDuhamelIdentity
import RHFormalization.GalerkinFreeHeatDiagonal
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
-- SENTINEL: decoded-full-sandwich-split-v2

namespace RHFormalization
noncomputable section
open Matrix MeasureTheory intervalIntegral
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **Full semigroup split (operator level).** The full integrand
`D(t-u)·(-V)·E(u)` splits into the diagonal order-1 term `D(t-u)·(-V)·D_exp(u)`
plus the quadratic remainder `D(t-u)·(-V)·(∫₀ᵘ sandwich)`, by substituting the
banked Duhamel identity for `E(u)` then distributing (`mul_add`). -/
theorem decodedGalerkinFullSandwich_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(decodedGalerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + decodedGalerkinV (N := N) δ qs w L)))
      = Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
          * (-(decodedGalerkinV (N := N) δ qs w L))
          * NormedSpace.exp (u • (-(galerkinK (N := N) L)))
        + Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
            * (-(decodedGalerkinV (N := N) δ qs w L))
            * (∫ s in (0:ℝ)..u,
                NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
                  * (-(decodedGalerkinV (N := N) δ qs w L))
                  * NormedSpace.exp (s • (-(galerkinK (N := N) L
                      + decodedGalerkinV (N := N) δ qs w L)))) := by
  have hid := decodedGalerkinDuhamel_identity (N := N) δ qs w L u
  -- E(u) = D_exp(u) + ∫ sandwich  (rearrange E - D = ∫ via abel)
  have hE : NormedSpace.exp (u • (-(galerkinK (N := N) L
              + decodedGalerkinV (N := N) δ qs w L)))
      = NormedSpace.exp (u • (-(galerkinK (N := N) L)))
        + (∫ s in (0:ℝ)..u,
            NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
              * (-(decodedGalerkinV (N := N) δ qs w L))
              * NormedSpace.exp (s • (-(galerkinK (N := N) L
                  + decodedGalerkinV (N := N) δ qs w L)))) := by
    rw [← hid]; abel
  rw [hE, mul_add]

#print axioms decodedGalerkinFullSandwich_split
end
end RHFormalization
