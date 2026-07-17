import RHFormalization.ShiftedLaplaceBRegularFinite
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# RHFormalization.ShiftedLaplaceSqrtBranch

Branch-control step for shifted/Laplace `hB_regular`.

Already banked:
- atomic shifted/Laplace term holomorphy;
- finite shifted/Laplace package holomorphy.

This repair deliberately does NOT use the nonexistent names
`Complex.sq_sqrt` or `sq_sqrt`.

We bank the branch holomorphy theorem from Mathlib's
`Complex.differentiableAt_sqrt` on `Complex.slitPlane`.

The square-root nonzero condition is kept as an explicit hypothesis here.
It will be proved in a separate file after we identify the exact complex sqrt-zero API.
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
    simpa [U] using Complex.isOpen_slitPlane.preimage hshift_cont

  have hdiffOn :
      DifferentiableOn ℂ shiftedLaplaceSqrt U := by
    intro w hw
    have hw_shift :
        shiftedLaplaceShift w ∈ Complex.slitPlane := by
      simpa [U] using hw

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
      AnalyticOnNhd ℂ shiftedLaplaceSqrt U :=
    DifferentiableOn.analyticOnNhd hdiffOn hUopen

  exact hAn z hzU

/--
Finite shifted/Laplace prime-power packages are holomorphic at `z` from the
explicit shifted slit-plane branch condition plus the nonzero sqrt condition.

The nonzero condition is separated because the previous file failed only from
guessing nonexistent complex sqrt-square lemma names.
-/
theorem finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch_sqrt_ne
    (I : Finset PrimePowerPair)
    (z : ℂ)
    (hz_shift :
      shiftedLaplaceShift z ∈ Complex.slitPlane)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      z :=
  finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shiftedSqrt
    I
    z
    (shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane z hz_shift)
    h_sqrt_ne

#print axioms shiftedLaplaceShift
#print axioms shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane
#print axioms finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch_sqrt_ne

end

end RHFormalization
