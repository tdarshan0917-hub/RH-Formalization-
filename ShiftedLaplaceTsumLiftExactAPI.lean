import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.ZpoleFromSeries
import RHFormalization.AnalyticWrappers
import RHFormalization.SphereUniformConvergence

/-!
Scratch-only exact API probe for the final shifted/Laplace hB_regular lift.

We are past:
- atomic term holomorphy;
- finite sums;
- sqrt branch;
- sqrt nonzero;
- Ω geometry.

Current blocker:
  finite canonical prime-power holomorphy on Ω
  ⇒ full shiftedLaplacePrimePackageAt.Bshared holomorphy on Ω.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check CanonicalPrimePowerPackage
#print CanonicalPrimePowerPackage

#check canonicalPrimePowerPackageFromKernelTsum
#check finiteCanonicalPrimePowerPackage
#check shiftedLaplacePrimePackageAt
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega

#check HolomorphicAtC
#check HolomorphicOnC
#check LocallyUniformConvergesOnC
#check TendstoLocallyUniformlyOn
#check TendstoUniformlyOn
#check tendstoUniformlyOn_tsum
#check tendstoUniformlyOn_of_tlu_isCompact
#check isOpen_Omega_proved

/-- Target shape, still scratch. -/
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

  have htsum_eq :
      (shiftedLaplacePrimePackageAt sigma0).Bshared z =
        ∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center z := by
    exact shiftedLaplacePrimePackageAt_Bshared_eq_tsum sigma0 z

  trivial

end

end RHFormalization
