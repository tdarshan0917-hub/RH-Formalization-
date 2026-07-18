import RHFormalization.ShiftedLaplaceSqrtBranch
import Mathlib.Analysis.RCLike.Sqrt

/-!
# RHFormalization.ShiftedLaplaceSqrtNonzero

Closes the nonzero side condition for the shifted/Laplace sqrt branch.

The previous repair failed because Lean did not rewrite

  sqrt x = 0

directly to

  x = 0.

This version squares the equality first and then lets `simp` rewrite the square
of the complex square-root.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check shiftedLaplaceShift
#check shiftedLaplaceSqrt
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch_sqrt_ne

/--
The shifted square-root is nonzero when its shifted argument is nonzero.
-/
theorem shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero
    (z : ℂ)
    (hz_shift_ne : shiftedLaplaceShift z ≠ 0) :
    shiftedLaplaceSqrt z ≠ 0 := by
  intro hsqrt_zero

  have hsq_zero :
      (shiftedLaplaceSqrt z) ^ 2 = 0 := by
    rw [hsqrt_zero]
    norm_num

  have hshift_zero :
      shiftedLaplaceShift z = 0 := by
    simpa [shiftedLaplaceSqrt, shiftedLaplaceShift] using hsq_zero

  exact hz_shift_ne hshift_zero

/--
Finite shifted/Laplace prime-power packages are holomorphic at `z` from
slit-plane membership and nonzero shifted argument.
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
  finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch_sqrt_ne
    I
    z
    hz_shift
    (shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero z hz_shift_ne)

#print axioms shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero
#print axioms finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch

end

end RHFormalization
