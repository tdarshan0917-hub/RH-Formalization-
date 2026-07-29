import RHFormalization.ShiftedLaplaceBRegularFromTLU
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check TendstoLocallyUniformlyOn
#check tendstoLocallyUniformlyOn_iff_forall_tendsto
#check IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto
#check TendstoUniformlyOn.tendstoLocallyUniformlyOn
#check TendstoLocallyUniformlyOn.mono
#check tendstoUniformlyOn_tsum

#check shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
#check shiftedLaplace_Bregular_from_tlu
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum

/-
Target remaining input after the latest green run:

TendstoLocallyUniformlyOn
  (fun I : Finset PrimePowerPair =>
    finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
  (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
  Filter.atTop
  Ω
-/

example
    (sigma0 : ℝ)
    (u : PrimePowerPair → ℝ)
    (hu : Summable u)
    (U : Set ℂ)
    (hbound :
      ∀ q : PrimePowerPair,
      ∀ s : ℂ,
        s ∈ U →
          ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ ≤ u q) :
    TendstoUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ =>
        ∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center s)
      Filter.atTop
      U := by
  simpa [finiteCanonicalPrimePowerPackage] using
    tendstoUniformlyOn_tsum hu hbound

end

end RHFormalization
