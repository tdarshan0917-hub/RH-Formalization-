import RHFormalization.ShiftedLaplaceRegularFromZeroDensity

/-!
# RHFormalization.ShiftedLaplaceBRegularAtomic

First real analytic step toward `hB_regular`.

Goal of the hB_regular track:

  ∀ z ∈ Ω,
    (∀ W, z ≠ W.s0) →
      HolomorphicAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        z

This file attacks the atomic term:
  s ↦ shiftedLaplaceHeatKernelC a s

The theorem below says the shifted/Laplace kernel term is holomorphic at z
whenever the shifted square-root branch is holomorphic and nonzero at z.

Next after this:
  prove the shifted square-root branch condition from z ∈ Ω,
  then lift from terms to the prime-power tsum.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- The shifted square-root appearing in the shifted/Laplace kernel. -/
abbrev shiftedLaplaceSqrt (s : ℂ) : ℂ :=
  Complex.sqrt (s + (1 / 4 : ℂ))

#check shiftedLaplaceHeatKernelC
#check shiftedLaplacePrimePackageAt
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum

/--
Atomic holomorphy of the shifted/Laplace heat kernel term, assuming the shifted
square-root branch is holomorphic and nonzero at the point.
-/
theorem shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
    (a : ℝ)
    (z : ℂ)
    (h_sqrt :
      HolomorphicAtC shiftedLaplaceSqrt z)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (fun s : ℂ => shiftedLaplaceHeatKernelC a s)
      z := by
  have hden :
      (2 : ℂ) * shiftedLaplaceSqrt z ≠ 0 := by
    exact mul_ne_zero (by norm_num) h_sqrt_ne

  unfold shiftedLaplaceHeatKernelC shiftedLaplaceSqrt
  fun_prop (disch := first | exact hden | norm_num)

/--
The weighted prime-power term is holomorphic under the same shifted-sqrt
hypotheses.
-/
theorem shiftedLaplaceWeightedTerm_holomorphicAt_of_shiftedSqrt
    (q : PrimePowerPair)
    (z : ℂ)
    (h_sqrt :
      HolomorphicAtC shiftedLaplaceSqrt z)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (fun s : ℂ =>
        q.weightC * shiftedLaplaceHeatKernelC q.center s)
      z := by
  simpa using
    (shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
      q.center z h_sqrt h_sqrt_ne).const_mul q.weightC

#print axioms shiftedLaplaceSqrt
#print axioms shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
#print axioms shiftedLaplaceWeightedTerm_holomorphicAt_of_shiftedSqrt

end

end RHFormalization
