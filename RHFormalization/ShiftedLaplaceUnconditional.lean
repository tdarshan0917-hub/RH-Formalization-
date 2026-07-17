import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceCapstoneTLU
import RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts

namespace RHFormalization

noncomputable section

open Complex Filter Topology

theorem RH_from_shiftedLaplace_meromorphy
    (sigma0 : ℝ)
    (hBmero :
      MeromorphicOnC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s) Ω)
    (hVopen : IsOpen shiftedLaplaceAbsConvRegion)
    (hVne : shiftedLaplaceAbsConvRegion.Nonempty)
    (hVsub : shiftedLaplaceAbsConvRegion ⊆ Ω)
    (hZpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (ZpoleSeries defaultZeroMultiplicityData)
          W.s0
          (groupedResidueCoeff defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W)))
    (hpoint :
      ∀ W : ZeroWitness,
        (Classical.choose
          (shiftedLaplace_hBpp_from_bridge sigma0
            (shiftedLaplace_bridge_from_meromorphy sigma0 hBmero hVopen hVne hVsub) W)) W.s0 +
          (Classical.choose (hZpp W)) W.s0 =
            (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0 +
              ZpoleSeries defaultZeroMultiplicityData W.s0)
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
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts)
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop Ω)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData defaultZeroExhaustion
            (ZpoleSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceHarchPackageFromHolo sigma0
              (shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
                sigma0 hsum ZF
                (shiftedLaplace_hcancel_from_grouped_principalParts sigma0
                  (fun W => defaultGroupedPoleClass defaultZeroMultiplicityData W)
                  (shiftedLaplace_hBpp_from_bridge sigma0
                    (shiftedLaplace_bridge_from_meromorphy sigma0 hBmero hVopen hVne hVsub))
                  hZpp hpoint)
                h_tlu))
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceHarchPackageFromHolo_split sigma0
              (shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
                sigma0 hsum ZF
                (shiftedLaplace_hcancel_from_grouped_principalParts sigma0
                  (fun W => defaultGroupedPoleClass defaultZeroMultiplicityData W)
                  (shiftedLaplace_hBpp_from_bridge sigma0
                    (shiftedLaplace_bridge_from_meromorphy sigma0 hBmero hVopen hVne hVsub))
                  hZpp hpoint)
                h_tlu))
            h_genuine_poles))) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_cancellation
    sigma0 Y hYC convergence poleSeriesMeromorphic h_genuine_poles
    h_Cshared_sigma_le hsum ZF
    (shiftedLaplace_hcancel_from_grouped_principalParts sigma0
      (fun W => defaultGroupedPoleClass defaultZeroMultiplicityData W)
      (shiftedLaplace_hBpp_from_bridge sigma0
        (shiftedLaplace_bridge_from_meromorphy sigma0 hBmero hVopen hVne hVsub))
      hZpp hpoint)
    h_tlu
    normalFormGroupedLayer

#print axioms RH_from_shiftedLaplace_meromorphy

end

end RHFormalization
