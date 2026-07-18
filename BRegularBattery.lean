import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability

open Complex Set Topology Filter Metric RHFormalization
open scoped BigOperators

-- Exact prime side after V9-explicit / EF5.
#check designedY_Cshared_Bshared_eq_tsum_global
#check designedY_Cshared_eq_concreteTsumPackage

-- Kernel objects.
#check displacementCanonicalKernel
#check heatKernelG
#check CanonicalKernelC

-- Existing prime-side summability candidates.
#check CanonicalPrimePowerHeatKernelGaussianCoreSummability
#check CanonicalPrimePowerWeightedSummabilityEnvelope
#check CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

-- Analytic wrappers.
#check HolomorphicAtC
#check HolomorphicOnC
#check holomorphicAtC_congr
#check AnalyticAt.congr
#check AnalyticAt.add
#check AnalyticAt.mul
#check AnalyticAt.const_mul
#check analyticAt_const
#check analyticAt_id

-- Local uniform / analytic limit possibilities.
#check TendstoLocallyUniformlyOn
#check TendstoUniformlyOn
#check tendstoUniformlyOn_tsum
#check TendstoLocallyUniformlyOn.analyticAt
#check TendstoLocallyUniformlyOn.analyticOn
#check TendstoUniformlyOn.analyticAt
#check TendstoUniformlyOn.analyticOn
#check AnalyticOn.tsum
#check AnalyticAt.tsum

-- Shape target only.
example
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC designedY.B.Cshared.Bshared z) :
    True := by
  trivial
