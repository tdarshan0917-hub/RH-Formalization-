import RHFormalization.ShiftedLaplaceBsharedMeromorphicFromIdentity
import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.ShiftedLaplaceRegionFacts
import RHFormalization.OmegaConnected
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

theorem shiftedLaplace_Bshared_meromorphicOn_Omega (sigma0 : ℝ) :
    MeromorphicOnC (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s) Ω := by
  have hmodel : MeromorphicOn shiftedLaplaceLogDerivModel Ω :=
    shiftedLaplaceLogDerivModel_meromorphicOn_Omega
  have hVopen : IsOpen shiftedLaplaceAbsConvRegion := shiftedLaplaceAbsConvRegion_isOpen
  have hagree : EqOn (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      shiftedLaplaceLogDerivModel shiftedLaplaceAbsConvRegion :=
    shiftedLaplace_Bshared_eqOn_model sigma0
  intro z hzΩ
  by_cases hzV : z ∈ shiftedLaplaceAbsConvRegion
  · have hnhd : shiftedLaplaceLogDerivModel
        =ᶠ[𝓝[≠] z] (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s) := by
      have : ∀ᶠ w in 𝓝 z, shiftedLaplaceLogDerivModel w
          = (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s) w := by
        filter_upwards [hVopen.mem_nhds hzV] with w hw using (hagree hw).symm
      exact this.filter_mono nhdsWithin_le_nhds
    exact (hmodel z hzΩ).congr hnhd
  · -- OFF REGION: the tsum diverges here; Lean's tsum returns 0. Test if it's meromorphic.
    -- Is the tsum actually = 0 in a neighborhood off the region? If so, 0 is meromorphic.
    sorry

#print axioms shiftedLaplace_Bshared_meromorphicOn_Omega

end
end RHFormalization
