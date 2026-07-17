import RHFormalization.ShiftedLaplaceCapstone
import RHFormalization.ShiftedLaplaceHoloLocalReduction

namespace RHFormalization

noncomputable section

open Complex

theorem RH_from_shiftedLaplace_localExtensions
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
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) W.s0)
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
              (shiftedLaplace_holo_from_localExtensions sigma0 h_witness h_regular))
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceHarchPackageFromHolo_split sigma0
              (shiftedLaplace_holo_from_localExtensions sigma0 h_witness h_regular))
            h_genuine_poles))) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_holo
    sigma0 Y hYC convergence poleSeriesMeromorphic h_genuine_poles
    h_Cshared_sigma_le
    (shiftedLaplace_holo_from_localExtensions sigma0 h_witness h_regular)
    normalFormGroupedLayer

#print axioms RH_from_shiftedLaplace_localExtensions

end

end RHFormalization
