import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.EtaPositivity

namespace RHFormalization

noncomputable section

open Complex

theorem RH_from_shiftedLaplace_holo
    (sigma0 : ℝ)
    (Y : DDetailedConstructionWithOperatorLegality)
    (hYC : Y.B.Cshared = shiftedLaplacePrimePackageAt sigma0)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (h_genuine_poles :
      ∀ W : ZeroWitness,
        HasGenuinePole (ZpoleSeries defaultZeroMultiplicityData) W.s0)
    (h_Cshared_sigma_le : (shiftedLaplacePrimePackageAt sigma0).sigma0 ≤ sigma0)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData defaultZeroExhaustion
            (ZpoleSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceHarchPackageFromHolo sigma0 h_holo)
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceHarchPackageFromHolo_split sigma0 h_holo)
            h_genuine_poles))) :
    RiemannHypothesis := by
  refine RH_current_frontier h_real_zero_free Y
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      defaultZeroMultiplicityData defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData)
      convergence poleSeriesMeromorphic
      (shiftedLaplaceHarchPackageFromHolo sigma0 h_holo)
      (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
      (shiftedLaplaceHarchPackageFromHolo_split sigma0 h_holo)
      h_genuine_poles
      normalFormGroupedLayer) ?_
  rw [hYC, buildHMeromorphicWithNormalFormPolesWithChosenCshared_Cshared_eq]

#print axioms RH_from_shiftedLaplace_holo

end

end RHFormalization
