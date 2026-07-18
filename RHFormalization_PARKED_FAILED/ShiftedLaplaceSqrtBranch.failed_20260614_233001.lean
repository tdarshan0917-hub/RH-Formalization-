import RHFormalization.ShiftedLaplaceBRegularFinite
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# RHFormalization.ShiftedLaplaceSqrtBranch

Branch-control step for shifted/Laplace `hB_regular`.

Already banked:
- atomic shifted/Laplace term holomorphy from
  `HolomorphicAtC shiftedLaplaceSqrt z` and `shiftedLaplaceSqrt z ≠ 0`;
- finite shifted/Laplace package holomorphy from the same branch hypotheses.

This file proves the square-root branch hypotheses from explicit shifted
slit-plane conditions:

  z + 1/4 ∈ Complex.slitPlane
  z + 1/4 ≠ 0.

The remaining geometric step after this file is:
  z ∈ Ω ⇒ z + 1/4 ∈ Complex.slitPlane ∧ z + 1/4 ≠ 0.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- The shifted argument used inside the shifted/Laplace square-root. -/
abbrev shiftedLaplaceShift (s : ℂ) : ℂ :=
  s + (1 / 4 : ℂ)

#check Complex.differentiableAt_sqrt
#check Complex.isOpen_slitPlane
#check DifferentiableOn.analyticOnNhd
#check Complex.sq_sqrt
#check sq_sqrt

/--
The shifted square-root is holomorphic at `z` when the shifted argument lies
on Mathlib's principal sqrt slit plane.
-/
theorem shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane
    (z : ℂ)
    (hz_shift :
      shiftedLaplaceShift z ∈ Complex.slitPlane) :
    HolomorphicAtC shiftedLaplaceSqrt z := by
  let U : Set ℂ :=
    {w : ℂ | shiftedLaplaceShift w ∈ Complex.slitPlane}

  have hzU : z ∈ U := hz_shift

  have hshift_cont : Continuous shiftedLaplaceShift := by
    unfold shiftedLaplaceShift
    fun_prop

  have hUopen : IsOpen U := by
    exact Complex.isOpen_slitPlane.preimage hshift_cont

  have hdiffOn :
      DifferentiableOn ℂ shiftedLaplaceSqrt U := by
    intro w hw
    have hw_shift :
        shiftedLaplaceShift w ∈ Complex.slitPlane := hw
    have hshift_at :
        DifferentiableAt ℂ shiftedLaplaceShift w := by
      unfold shiftedLaplaceShift
      fun_prop
    have hsqrt_at :
        DifferentiableAt ℂ shiftedLaplaceSqrt w := by
      simpa [shiftedLaplaceSqrt, shiftedLaplaceShift] using
        (Complex.differentiableAt_sqrt hw_shift).comp w hshift_at
    exact hsqrt_at.differentiableWithinAt

  have hAn :
      AnalyticOnNhd ℂ shiftedLaplaceSqrt U := by
    first
      | exact hdiffOn.analyticOnNhd hUopen
      | exact hdiffOn.analyticOnNhd

  exact hAn z hzU

/--
The shifted square-root is nonzero when the shifted argument is nonzero.
-/
theorem shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero
    (z : ℂ)
    (hz_shift_ne :
      shiftedLaplaceShift z ≠ 0) :
    shiftedLaplaceSqrt z ≠ 0 := by
  intro hzero

  have hsqsqrt :
      (shiftedLaplaceSqrt z) ^ 2 = shiftedLaplaceShift z := by
    first
      | simpa [shiftedLaplaceSqrt, shiftedLaplaceShift] using
          (Complex.sq_sqrt (shiftedLaplaceShift z))
      | simpa [shiftedLaplaceSqrt, shiftedLaplaceShift] using
          (sq_sqrt (shiftedLaplaceShift z))

  have hshift_zero :
      shiftedLaplaceShift z = 0 := by
    rw [← hsqsqrt]
    simp [hzero]

  exact hz_shift_ne hshift_zero

/--
Finite shifted/Laplace prime-power packages are holomorphic at `z` from the
explicit shifted slit-plane branch conditions.
-/
theorem finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch
    (I : Finset PrimePowerPair)
    (z : ℂ)
    (hz_shift :
      shiftedLaplaceShift z ∈ Complex.slitPlane)
    (hz_shift_ne :
      shiftedLaplaceShift z ≠ 0) :
    HolomorphicAtC
      (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      z :=
  finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shiftedSqrt
    I
    z
    (shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane z hz_shift)
    (shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero z hz_shift_ne)

#print axioms shiftedLaplaceShift
#print axioms shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane
#print axioms shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero
#print axioms finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch

end

end RHFormalization
