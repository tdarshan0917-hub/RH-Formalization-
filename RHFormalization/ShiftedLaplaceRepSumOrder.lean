import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.ShiftedLaplaceBsharedMeromorphicFromIdentity
import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.ShiftedLaplaceRegionFacts
import RHFormalization.OmegaConnected
import RHFormalization.PrincipalPartEventuallyEq
import Mathlib.Analysis.Meromorphic.Order

namespace RHFormalization
noncomputable section
open Complex Filter Topology

/-- At each witness, `Bshared + ZpoleRep` has nonnegative meromorphic order.
The opposite simple poles cancel, so on the punctured neighborhood the sum
equals the analytic regular-part sum `hF + hG`; meromorphic order depends only
on the punctured neighborhood, so it inherits the nonnegative order of an
analytic function. Honest replacement for the false `hpoint`. -/
theorem repSum_meromorphicOrderAt_nonneg
    (sigma0 : ℝ) (W : ZeroWitness)
    (hBpp : HasPrincipalPartAtC
      (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
      W.s0 ((zetaZeroMult W.ρ : ℂ))) :
    0 ≤ meromorphicOrderAt
          (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 := by
  classical
  obtain ⟨hF, hF_an, hF_eq⟩ := hBpp
  obtain ⟨hG, hG_an, hG_eq⟩ := hZpp_rep
  have hpunct : (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
      + ZpoleRepSeries defaultZeroMultiplicityData s)
      =ᶠ[𝓝[≠] W.s0] (fun s => hF s + hG s) := by
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [hF_eq, hG_eq] with w hFw hGw hwne
    have hBe := hFw hwne
    have hZe := hGw hwne
    show (shiftedLaplacePrimePackageAt sigma0).Bshared w
        + ZpoleRepSeries defaultZeroMultiplicityData w = hF w + hG w
    rw [hBe, hZe]
    ring
  have hAn : AnalyticAt ℂ (fun s => hF s + hG s) W.s0 := hF_an.add hG_an
  rw [meromorphicOrderAt_congr hpunct]
  exact hAn.meromorphicOrderAt_nonneg

#print axioms repSum_meromorphicOrderAt_nonneg

end
end RHFormalization
