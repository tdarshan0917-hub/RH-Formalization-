import RHFormalization.ShiftedLaplaceBRegularFinite

/-!
# ShiftedLaplaceSqrtBranchProbe

Scratch only.

We have already banked:
- shifted/Laplace atomic term holomorphy;
- finite shifted/Laplace prime-power sum holomorphy.

Next target:
  z ∈ Ω →
    HolomorphicAtC shiftedLaplaceSqrt z ∧ shiftedLaplaceSqrt z ≠ 0.

This probe asks Lean/mathlib what exact side condition `Complex.sqrt` wants.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check shiftedLaplaceSqrt
#check shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
#check shiftedLaplaceFinsetWeightedSum_holomorphicAt_of_shiftedSqrt
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shiftedSqrt

/--
Probe 1: can `fun_prop` prove shifted sqrt holomorphy directly from z ∈ Ω?
If this fails, the error should expose the exact branch-cut side condition.
-/
theorem shiftedLaplaceSqrt_holomorphicAt_probe
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    HolomorphicAtC shiftedLaplaceSqrt z := by
  unfold shiftedLaplaceSqrt
  fun_prop

end

end RHFormalization
