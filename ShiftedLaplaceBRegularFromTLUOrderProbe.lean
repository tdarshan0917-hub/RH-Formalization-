import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.ShiftedLaplaceRegularFromZeroDensity
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check TendstoLocallyUniformlyOn.differentiableOn
#check DifferentiableOn.analyticOnNhd
#check isOpen_Omega_proved
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega

example
    (sigma0 : ℝ)
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop
        Ω)
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    HolomorphicAtC
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      z := by
  have hdiff_finite_eventually :
      ∀ᶠ I in (Filter.atTop : Filter (Finset PrimePowerPair)),
        DifferentiableOn ℂ
          (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
          Ω := by
    exact Filter.Eventually.of_forall (fun I => by
      intro w hwΩ
      have hAt :
          HolomorphicAtC
            (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
            w :=
        finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
          I w hwΩ
      exact hAt.differentiableAt.differentiableWithinAt)

  have hdiff :
      DifferentiableOn ℂ
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Ω := by
    exact
      TendstoLocallyUniformlyOn.differentiableOn
        h_tlu
        hdiff_finite_eventually
        isOpen_Omega_proved

  exact (hdiff.analyticOnNhd isOpen_Omega_proved) z hzΩ

end

end RHFormalization
