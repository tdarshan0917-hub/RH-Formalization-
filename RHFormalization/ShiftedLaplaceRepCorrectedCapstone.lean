import RHFormalization.ShiftedLaplaceCapstone
import RHFormalization.ShiftedLaplaceRepCorrectedHarch
import RHFormalization.ShiftedLaplaceRepCapstone

namespace RHFormalization
noncomputable section
open Complex

/-- The corrected Rep capstone: derives RH from the principal-part data and the
regular-branch holomorphy, via the corrected Harch package (Brick C/D) — bypassing
the false raw-sum `h_holo` (which is unprovable because the raw sum is discontinuous
at witnesses). The honest H-side endpoint. -/
theorem RH_from_shiftedLaplace_rep_holo_corrected
    (sigma0 : ℝ) (hsigma : 0 ≤ sigma0)
    (ZF : ZetaZeroFacts)
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
    (hBpp : ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (h_regular : ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (repRaw sigma0) z)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData E
            (ZpoleRepSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceRepCorrectedHarchPackage sigma0 ZF hBpp hZpp_rep h_regular)
            (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
            (fun s hs => shiftedLaplaceRepCorrectedHarchPackage_split
              sigma0 ZF hsigma hBpp hZpp_rep h_regular s hs)
            h_genuine_poles))) :
    RiemannHypothesis := by
  refine RH_current_frontier h_real_zero_free Y
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      defaultZeroMultiplicityData E
      (ZpoleRepSeries defaultZeroMultiplicityData)
      convergence poleSeriesMeromorphic
      (shiftedLaplaceRepCorrectedHarchPackage sigma0 ZF hBpp hZpp_rep h_regular)
      (shiftedLaplacePrimePackageAt sigma0) sigma0 h_Cshared_sigma_le
      (fun s hs => shiftedLaplaceRepCorrectedHarchPackage_split
        sigma0 ZF hsigma hBpp hZpp_rep h_regular s hs)
      h_genuine_poles
      normalFormGroupedLayer) ?_
  rw [hYC, buildHMeromorphicWithNormalFormPolesWithChosenCshared_Cshared_eq]

#print axioms RH_from_shiftedLaplace_rep_holo_corrected

end
end RHFormalization
