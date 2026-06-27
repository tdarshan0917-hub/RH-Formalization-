import RHFormalization.RealPrimeY
import RHFormalization.ShiftedLaplaceRepCorrectedCapstone
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/-
Real-prime wrapper through the corrected Rep H-side.

This is the right route now:
  realPrimeY supplies Y
  RH_from_shiftedLaplace_rep_holo_corrected supplies the corrected H-side closure

No selectedFiniteOperatorLayer.
No resolventOperatorLayer.
No ZpoleSeries / old H route.
-/
theorem realPrime_RH_rep_corrected
    (μ : Fin N → ℝ)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
          (primePerturbedOperatorLayerAligned μ))
    (FH RH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FH :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∀ (ε : ℝ), 0 < ε →
          ∀ᶠ (n : ℕ) in Filter.atTop, ∀ s ∈ K,
            dist ((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (S.alpha n) s) (FH s) < ε)
    (h_R_stage_to_RH :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∀ (ε : ℝ), 0 < ε →
          ∀ᶠ (n : ℕ) in Filter.atTop, ∀ s ∈ K,
            dist ((primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (S.alpha n) s) (RH s) < ε)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ (primePerturbedOperatorLayerAligned μ).toStagePackage.sigma0)

    -- corrected Rep H-side inputs
    (ZF : ZetaZeroFacts)
    (E : ZeroExhaustion)
    (hYC :
      (realPrimeY μ S FH RH h_FH_holo h_RH_holo
        h_F_stage_to_FH h_R_stage_to_RH h_R_stage_bound hσ).B.Cshared =
        shiftedLaplacePrimePackageAt 1)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (h_genuine_poles :
      ∀ W : ZeroWitness,
        HasGenuinePole (ZpoleRepSeries defaultZeroMultiplicityData) W.s0)
    (h_Cshared_sigma_le : (shiftedLaplacePrimePackageAt 1).sigma0 ≤ 1)
    (hBpp : ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (h_regular : ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (repRaw 1) z)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData E
            (ZpoleRepSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (shiftedLaplaceRepCorrectedHarchPackage 1 ZF hBpp hZpp_rep h_regular)
            (shiftedLaplacePrimePackageAt 1) 1 h_Cshared_sigma_le
            (fun s hs => shiftedLaplaceRepCorrectedHarchPackage_split
              1 ZF (by norm_num) hBpp hZpp_rep h_regular s hs)
            h_genuine_poles))) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_rep_holo_corrected
    1
    (by norm_num)
    ZF
    E
    (realPrimeY μ S FH RH h_FH_holo h_RH_holo
      h_F_stage_to_FH h_R_stage_to_RH h_R_stage_bound hσ)
    hYC
    convergence
    poleSeriesMeromorphic
    h_genuine_poles
    h_Cshared_sigma_le
    hBpp
    hZpp_rep
    h_regular
    normalFormGroupedLayer

#print axioms realPrime_RH_rep_corrected

end
end RHFormalization
