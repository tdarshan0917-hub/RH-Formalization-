import RHFormalization.ShiftedLaplaceLocalExtensionEndpoint
import RHFormalization.ShiftedLaplaceWitnessFromBridge

namespace RHFormalization

noncomputable section

open Complex Filter Topology

theorem RH_from_shiftedLaplace_bridge
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
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData defaultZeroExhaustion
            (ZpoleSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceHarchPackageFromHolo sigma0
              (shiftedLaplace_holo_from_localExtensions sigma0
                (shiftedLaplace_h_witness_from_bridge sigma0 hBmero hVopen hVne hVsub hZpp hpoint)
                h_regular))
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceHarchPackageFromHolo_split sigma0
              (shiftedLaplace_holo_from_localExtensions sigma0
                (shiftedLaplace_h_witness_from_bridge sigma0 hBmero hVopen hVne hVsub hZpp hpoint)
                h_regular))
            h_genuine_poles))) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_localExtensions
    sigma0 Y hYC convergence poleSeriesMeromorphic h_genuine_poles
    h_Cshared_sigma_le
    (shiftedLaplace_h_witness_from_bridge sigma0 hBmero hVopen hVne hVsub hZpp hpoint)
    h_regular
    normalFormGroupedLayer

#print axioms RH_from_shiftedLaplace_bridge

end

end RHFormalization
