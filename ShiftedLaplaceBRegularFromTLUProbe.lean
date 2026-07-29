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
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum
#check shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity

/--
Probe: local uniform convergence of the finite shifted/Laplace packages to the
shifted/Laplace Bshared function implies pointwise holomorphy on Ω.
-/
theorem shiftedLaplace_Bshared_holomorphicAt_of_tlu_probe
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
    first
      | exact h_tlu.differentiableOn isOpen_Omega_proved hdiff_finite_eventually
      | exact TendstoLocallyUniformlyOn.differentiableOn
          h_tlu isOpen_Omega_proved hdiff_finite_eventually
      | exact h_tlu.differentiableOn hdiff_finite_eventually isOpen_Omega_proved

  exact (hdiff.analyticOnNhd isOpen_Omega_proved) z hzΩ

end

end RHFormalization
