import RHFormalization.ShiftedLaplaceOmegaGeometry

/-!
# ShiftedLaplaceBRegularTsumLiftProbe

Scratch-only probe for the final hB_regular lift.

Already banked:
- finite shifted/Laplace package holomorphy on Ω:
  `finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega`

Remaining:
- lift finite prime-power sums to the full shifted/Laplace `Bshared` tsum.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check shiftedLaplacePrimePackageAt
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum
#check shiftedLaplacePrimePackage_Bshared_eq_tsum
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
#check shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity

#print CanonicalPrimePowerPackage
#print PrimePowerPair
#print HolomorphicAtC
#print HolomorphicOnC

/-- Target shape for the next real theorem. This should remain as a probe. -/
example
    (sigma0 : ℝ)
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    True := by
  have hfinite :
      ∀ I : Finset PrimePowerPair,
        HolomorphicAtC
          (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
          z := by
    intro I
    exact finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
      I z hzΩ
  trivial

end

end RHFormalization
