import RHFormalization.ShiftedLaplaceCapstone
import RHFormalization.ShiftedLaplaceRepCapstone
import RHFormalization.ModelRepCorrectedHarch
import RHFormalization.ShiftedLaplaceModelPackageProbe

namespace RHFormalization
noncomputable section
open Complex

/-- **The model corrected Rep capstone — H-side fully discharged.** Derives RH
using the MODEL B-side, where all three H-side inputs are proven theorems
(`hBpp` = model-PP, `hZpp_rep` = `shiftedLaplace_hZpp_rep_free`, `h_regular` =
model Rep regularity), threaded through the hypothesis-free corrected Harch
package `modelRepCorrectedHarchPackage`. No `hpoint`, no keystone, no raw-sum
`h_holo`. The remaining hypotheses are the D-side construction (`hYC`), the Zpole
convergence/meromorphy/genuine-poles, and the grouped-normal-form layer. -/
theorem RH_from_model_corrected
    (sigma0 : ℝ) (hsigma : 0 ≤ sigma0)
    (ZF : ZetaZeroFacts)
    (E : ZeroExhaustion)
    (Y : DDetailedConstructionWithOperatorLegality)
    (hYC : Y.B.Cshared = shiftedLaplaceModelPackageAt sigma0)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (h_genuine_poles :
      ∀ W : ZeroWitness,
        HasGenuinePole (ZpoleRepSeries defaultZeroMultiplicityData) W.s0)
    (h_Cshared_sigma_le : (shiftedLaplaceModelPackageAt sigma0).sigma0 ≤ sigma0)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData E
            (ZpoleRepSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (modelRepCorrectedHarchPackage ZF)
            (shiftedLaplaceModelPackageAt sigma0) sigma0 h_Cshared_sigma_le
            (fun s hs => modelRepCorrectedHarchPackage_split
              ZF sigma0 hsigma s hs)
            h_genuine_poles))) :
    RiemannHypothesis := by
  refine RH_current_frontier h_real_zero_free Y
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      defaultZeroMultiplicityData E
      (ZpoleRepSeries defaultZeroMultiplicityData)
      convergence poleSeriesMeromorphic
      (modelRepCorrectedHarchPackage ZF)
      (shiftedLaplaceModelPackageAt sigma0) sigma0 h_Cshared_sigma_le
      (fun s hs => modelRepCorrectedHarchPackage_split
        ZF sigma0 hsigma s hs)
      h_genuine_poles
      normalFormGroupedLayer) ?_
  rw [hYC, buildHMeromorphicWithNormalFormPolesWithChosenCshared_Cshared_eq]

#print axioms RH_from_model_corrected

end
end RHFormalization
