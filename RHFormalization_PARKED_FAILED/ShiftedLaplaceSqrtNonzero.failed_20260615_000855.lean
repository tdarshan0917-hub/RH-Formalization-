import RHFormalization.ShiftedLaplaceSqrtBranch
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Data.Complex.Exponential

/-!
# RHFormalization.ShiftedLaplaceSqrtNonzero

Closes the nonzero side condition for the shifted/Laplace sqrt branch.

The local Mathlib API does not expose:
  Complex.sqrt_eq_zero
  Complex.sqrt_ne_zero
  Complex.sq_sqrt
  RCLike.sq_sqrt

But it does expose:
  Complex.sqrt_eq_exp

So we prove nonzero by rewriting the complex sqrt of a nonzero argument as
an exponential, and then using nonvanishing of `Complex.exp`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check shiftedLaplaceShift
#check shiftedLaplaceSqrt
#check Complex.sqrt_eq_exp
#check Complex.exp_ne_zero
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch_sqrt_ne

/--
The shifted square-root is nonzero when its shifted argument is nonzero.
-/
theorem shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero
    (z : ℂ)
    (hz_shift_ne : shiftedLaplaceShift z ≠ 0) :
    shiftedLaplaceSqrt z ≠ 0 := by
  have hsqrt_exp :
      shiftedLaplaceSqrt z =
        Complex.exp (Complex.log (shiftedLaplaceShift z) / 2) := by
    simpa [shiftedLaplaceSqrt, shiftedLaplaceShift] using
      (Complex.sqrt_eq_exp (z := shiftedLaplaceShift z) hz_shift_ne)

  rw [hsqrt_exp]
  exact Complex.exp_ne_zero _

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
