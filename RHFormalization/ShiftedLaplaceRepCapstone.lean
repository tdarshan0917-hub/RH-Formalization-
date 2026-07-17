import RHFormalization.ShiftedLaplaceCapstone
import RHFormalization.ShiftedLaplaceRepHarch

namespace RHFormalization
noncomputable section
open Complex

theorem RH_from_shiftedLaplace_rep_holo
    (sigma0 : ℝ)
    (E : ZeroExhaustion)
    (Y : DDetailedConstructionWithOperatorLegality)
    (hYC : Y.B.Cshared = shiftedLaplacePrimePackageAt sigma0)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (h_genuine_poles :
      ∀ W : ZeroWitness,
        HasGenuinePole (ZpoleRepSeries defaultZeroMultiplicityData) W.s0)
    (h_Cshared_sigma_le : (shiftedLaplacePrimePackageAt sigma0).sigma0 ≤ sigma0)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleRepSeries defaultZeroMultiplicityData s)
        Ω)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData E
            (ZpoleRepSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceRepHarchPackageFromHolo sigma0 h_holo)
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceRepHarchPackageFromHolo_split sigma0 h_holo)
            h_genuine_poles))) :
    RiemannHypothesis := by
  refine RH_current_frontier h_real_zero_free Y
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      defaultZeroMultiplicityData E
      (ZpoleRepSeries defaultZeroMultiplicityData)
      convergence poleSeriesMeromorphic
      (shiftedLaplaceRepHarchPackageFromHolo sigma0 h_holo)
      (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
      (shiftedLaplaceRepHarchPackageFromHolo_split sigma0 h_holo)
      h_genuine_poles
      normalFormGroupedLayer) ?_
  rw [hYC, buildHMeromorphicWithNormalFormPolesWithChosenCshared_Cshared_eq]

#print axioms RH_from_shiftedLaplace_rep_holo

end
end RHFormalization
