import RHFormalization.ShiftedLaplaceBRegularFromTLU
import Mathlib.Analysis.Meromorphic.Basic

namespace RHFormalization

noncomputable section

open Complex

theorem shiftedLaplace_Bshared_meromorphicOn_Omega_of_tlu
    (sigma0 : ℝ)
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop
        Ω) :
    MeromorphicOnC
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s) Ω := by
  intro z hz
  exact (shiftedLaplace_Bshared_holomorphicAt_of_tlu sigma0 h_tlu z hz).meromorphicAt

#print axioms shiftedLaplace_Bshared_meromorphicOn_Omega_of_tlu

end

end RHFormalization
