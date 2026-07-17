import RHFormalization.QuadRemainderTraceIntegralReduce
import RHFormalization.GalerkinDuhamelUniformBound
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

/-- Step 1(a) second piece probe: bound the remainder integrand pointwise in s
    by product of operator norms. -/
theorem quadRemainder_integrand_abs_le
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t u s : ℝ) :
    ‖((Matrix.diagonal fun m => heatWeight L (t - u) m)
        * (-(galerkinV (N := N) δ qs w L))
        * (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (s • -(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L))))‖
      ≤ ‖(Matrix.diagonal fun m => heatWeight L (t - u) m)
          * (-(galerkinV (N := N) δ qs w L))‖
        * ‖NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (s • -(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L))‖ := by
  exact norm_mul_le _ _

#print axioms quadRemainder_integrand_abs_le

end

end RHFormalization
