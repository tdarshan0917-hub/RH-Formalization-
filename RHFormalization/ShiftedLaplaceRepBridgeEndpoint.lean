import RHFormalization.ShiftedLaplaceRepCapstone
import RHFormalization.ShiftedLaplaceRepHolo
import RHFormalization.ShiftedLaplaceRepWitnessFromBridge

namespace RHFormalization
noncomputable section
open Complex

theorem RH_from_shiftedLaplace_rep_bridge
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
    (hBpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
          W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (hpoint :
      ∀ W : ZeroWitness,
        (Classical.choose (hBpp W)) W.s0 +
          (Classical.choose (hZpp_rep W)) W.s0 =
            (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0 +
              ZpoleRepSeries defaultZeroMultiplicityData W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
              + ZpoleRepSeries defaultZeroMultiplicityData s) z)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData E
            (ZpoleRepSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceRepHarchPackageFromHolo sigma0
              (shiftedLaplace_rep_holo_from_localExtensions sigma0
                (shiftedLaplace_repWitness_from_principalParts sigma0 hBpp hZpp_rep hpoint)
                h_regular))
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (shiftedLaplaceRepHarchPackageFromHolo_split sigma0
              (shiftedLaplace_rep_holo_from_localExtensions sigma0
                (shiftedLaplace_repWitness_from_principalParts sigma0 hBpp hZpp_rep hpoint)
                h_regular))
            h_genuine_poles))) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_rep_holo
    sigma0 E Y hYC convergence poleSeriesMeromorphic h_genuine_poles
    h_Cshared_sigma_le
    (shiftedLaplace_rep_holo_from_localExtensions sigma0
      (shiftedLaplace_repWitness_from_principalParts sigma0 hBpp hZpp_rep hpoint)
      h_regular)
    normalFormGroupedLayer

#print axioms RH_from_shiftedLaplace_rep_bridge

end
end RHFormalization
