import RHFormalization.QuadRemainderIntegrandBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Split the E(s) sandwich norm into its three operator-norm factors. -/
theorem quadRemainder_sandwich_norm_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L u s : ℝ) :
    ‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))‖
      ≤ ‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)‖
        * ‖galerkinV (N := N) δ qs w L‖
        * ‖NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))‖ := by
  calc ‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))‖
      ≤ ‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
          * (-(galerkinV (N := N) δ qs w L))‖
        * ‖NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))‖ := norm_mul_le _ _
    _ ≤ (‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)‖
          * ‖(-(galerkinV (N := N) δ qs w L))‖)
        * ‖NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))‖ := by
        apply mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)‖
        * ‖galerkinV (N := N) δ qs w L‖
        * ‖NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))‖ := by rw [norm_neg]

#print axioms quadRemainder_sandwich_norm_split

end

end RHFormalization
