import RHFormalization.ShiftedLaplaceBRegularAtomic

/-!
# RHFormalization.ShiftedLaplaceBRegularFinite

Finite-sum lift for the shifted/Laplace B-regular branch.

The previous version failed because the parser rejected the notation

  ∑ q in I, ...

in this file context. This version avoids that notation and uses

  I.sum (fun q => ...)

directly.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Finite sums of shifted/Laplace weighted prime-power terms are holomorphic under
the same shifted-sqrt branch hypotheses.
-/
theorem shiftedLaplaceFinsetWeightedSum_holomorphicAt_of_shiftedSqrt
    (I : Finset PrimePowerPair)
    (z : ℂ)
    (h_sqrt :
      HolomorphicAtC shiftedLaplaceSqrt z)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (fun s : ℂ =>
        I.sum
          (fun q : PrimePowerPair =>
            q.weightC * shiftedLaplaceHeatKernelC q.center s))
      z := by
  classical
  refine Finset.induction_on I ?h_empty ?h_insert
  · simpa using
      (analyticAt_const :
        HolomorphicAtC (fun _ : ℂ => (0 : ℂ)) z)
  · intro q I hq hI
    have hq_holo :
        HolomorphicAtC
          (fun s : ℂ =>
            q.weightC * shiftedLaplaceHeatKernelC q.center s)
          z :=
      shiftedLaplaceWeightedTerm_holomorphicAt_of_shiftedSqrt
        q z h_sqrt h_sqrt_ne
    simpa [Finset.sum_insert, hq] using hq_holo.add hI

/--
The finite canonical prime-power package built from the shifted/Laplace kernel
is holomorphic at z under the shifted-sqrt branch hypotheses.
-/
theorem finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shiftedSqrt
    (I : Finset PrimePowerPair)
    (z : ℂ)
    (h_sqrt :
      HolomorphicAtC shiftedLaplaceSqrt z)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      z := by
  simpa [finiteCanonicalPrimePowerPackage] using
    shiftedLaplaceFinsetWeightedSum_holomorphicAt_of_shiftedSqrt
      I z h_sqrt h_sqrt_ne

#print axioms shiftedLaplaceFinsetWeightedSum_holomorphicAt_of_shiftedSqrt
#print axioms finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shiftedSqrt

end

end RHFormalization
