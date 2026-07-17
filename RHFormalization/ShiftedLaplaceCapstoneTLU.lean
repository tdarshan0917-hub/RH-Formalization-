import RHFormalization.ShiftedLaplaceCapstone
import RHFormalization.ShiftedLaplaceBRegularFromTLU

namespace RHFormalization

noncomputable section

open Complex Filter

theorem RH_from_shiftedLaplace_cancellation
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
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts)
    (hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W)
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop
        Ω)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData defaultZeroExhaustion
            (ZpoleSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceHarchPackageFromHolo sigma0
              (shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
                sigma0 hsum ZF hcancel h_tlu))
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceHarchPackageFromHolo_split sigma0
              (shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
                sigma0 hsum ZF hcancel h_tlu))
            h_genuine_poles))) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_holo
    sigma0 Y hYC convergence poleSeriesMeromorphic h_genuine_poles
    h_Cshared_sigma_le
    (shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
      sigma0 hsum ZF hcancel h_tlu)
    normalFormGroupedLayer

#print axioms RH_from_shiftedLaplace_cancellation

end

end RHFormalization
