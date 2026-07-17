import RHFormalization.GalerkinDuhamelIdentity
import RHFormalization.DBFFO1SandwichTraceDecomposition
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Correct pointwise split using Duhamel on E(r). -/
theorem galerkinOrder2Pointwise_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (t u r : ℝ) :
    Matrix.trace (
      NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (r • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))
    )
    =
    Matrix.trace (
      NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (r • (-(galerkinK (N := N) L)))
    )
    +
    Matrix.trace (
      NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * (∫ σ in (0:ℝ)..r,
            NormedSpace.exp ((r - σ) • (-(galerkinK (N := N) L)))
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (σ • (-(galerkinK (N := N) L
                  + galerkinV (N := N) δ qs w L))))
    ) := by

  -- expand E(r)
  have hid :=
    galerkinDuhamel_identity (N := N) δ qs w L r

  -- rewrite to E = D + integral
  have hE :
      NormedSpace.exp (r • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))
      =
      NormedSpace.exp (r • (-(galerkinK (N := N) L)))
      +
      ∫ σ in (0:ℝ)..r,
        NormedSpace.exp ((r - σ) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp (σ • (-(galerkinK (N := N) L
              + galerkinV (N := N) δ qs w L))) := by
    have h := (sub_eq_iff_eq_add.mp hid)
    exact h.trans (add_comm _ _)

  -- substitute
  rw [hE]

  -- distribute multiplication
  rw [mul_add, Matrix.trace_add]

#print axioms galerkinOrder2Pointwise_split

end

end RHFormalization
