import RHFormalization.ShiftedLaplaceTLUFromLocalMTest
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCore
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummability
import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

/-!
Scratch audit for constructing:

  ShiftedLaplaceLocalMTestData

We need local majorants for:

  ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖

on neighborhoods inside Ω.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check ShiftedLaplaceLocalMTestData
#check shiftedLaplaceHeatKernelC
#check shiftedLaplaceShift
#check shiftedLaplaceSqrt
#check shiftedLaplaceShift_mem_slitPlane_of_mem_Omega
#check shiftedLaplaceShift_ne_zero_of_mem_Omega

#check PrimePowerPair.weightC
#check PrimePowerPair.center
#check PrimePowerPair.natValue
#check IsPrimePowerPair

-- Existing Gaussian/heat-kernel summability and norm-bound tools:
#check heatKernelG
#check canonicalPrimePowerPackageFromKernelTsum

/-- Target shape: a local bound theorem we need to construct next. -/
example
    (z0 : {z : ℂ // z ∈ Ω}) :
    True := by
  trivial

end

end RHFormalization
