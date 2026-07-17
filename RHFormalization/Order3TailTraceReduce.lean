import RHFormalization.Order2PointwiseSplit
import RHFormalization.QuadRemainderTraceIntegralReduce
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

/--
Trace-of-integral reduction for the order-3 tail term.

This is consumed by:
`galerkinOrder2SandwichTrace_abs_le`

to reduce the remaining perturbed tail to a pointwise integrand.
-/
theorem galerkinOrder3Tail_trace_le_integral_abs
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u r : ℝ)
    (hr : 0 ≤ r) :
    |(
      NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        *
        (∫ σ in (0:ℝ)..r,
            NormedSpace.exp ((r - σ) • (-(galerkinK (N := N) L)))
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (σ • (-(galerkinK (N := N) L
                  + galerkinV (N := N) δ qs w L))))
    ).trace|
      ≤
    ∫ σ in (0:ℝ)..r,
      |(
        NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          *
          (NormedSpace.exp ((r - σ) • (-(galerkinK (N := N) L)))
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (σ • (-(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L))))
      ).trace| := by

  -- package outer product
  set A :=
    NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
      * (-(galerkinV (N := N) δ qs w L))
      * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
      * (-(galerkinV (N := N) δ qs w L))

  set F : ℝ → Matrix (Fin N) (Fin N) ℝ :=
    fun σ =>
      NormedSpace.exp ((r - σ) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (σ • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))

  have hcontF : Continuous F := by
    fun_prop

  have hint :
      IntervalIntegrable F volume 0 r :=
    hcontF.intervalIntegrable 0 r

  have hcontAF : Continuous fun σ => A * F σ := by
    fun_prop

  have hstep :
      A * (∫ σ in (0:ℝ)..r, F σ)
        = ∫ σ in (0:ℝ)..r, A * F σ := by
    have h :=
      (ContinuousLinearMap.intervalIntegral_comp_comm
        ((LinearMap.mulLeft ℝ A).toContinuousLinearMap) hint)
    simpa [LinearMap.mulLeft_apply] using h.symm

  change
    |(A * (∫ σ in (0:ℝ)..r, F σ)).trace|
      ≤
    ∫ σ in (0:ℝ)..r, |(A * F σ).trace|

  rw [hstep]

  rw [trace_integral_comm_real (N := N) r (fun σ => A * F σ) hcontAF]

  exact intervalIntegral.abs_integral_le_integral_abs hr

#print axioms galerkinOrder3Tail_trace_le_integral_abs

end

end RHFormalization
