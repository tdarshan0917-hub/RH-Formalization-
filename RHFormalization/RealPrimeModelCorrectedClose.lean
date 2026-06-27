import RHFormalization.ModelRepCorrectedCapstone
import RHFormalization.RealPrimeY
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/--
Real-prime close through the MODEL-CORRECTED H-side.

Purpose:
  avoid the `FinalRHAssembly` / `hpoint` cancellation route.

This is the assembly endpoint we should use now.
The remaining inputs are exactly the true assembly inputs.
-/
theorem realPrime_RH_model_corrected
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

    -- H/model-corrected side inputs
    (ZF : ZetaZeroFacts)
    (E : ZeroExhaustion)
    (hYC :
      (realPrimeY μ S FH RH h_FH_holo h_RH_holo
        h_F_stage_to_FH h_R_stage_to_RH h_R_stage_bound hσ).B.Cshared =
        shiftedLaplaceModelPackageAt 1)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData E
        (ZpoleRepSeries defaultZeroMultiplicityData))
    (h_genuine_poles :
      ∀ W : ZeroWitness,
        HasGenuinePole (ZpoleRepSeries defaultZeroMultiplicityData) W.s0)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            defaultZeroMultiplicityData E
            (ZpoleRepSeries defaultZeroMultiplicityData)
            convergence poleSeriesMeromorphic
            (modelRepCorrectedHarchPackage ZF)
            (shiftedLaplaceModelPackageAt 1) 1 (by rfl)
            (fun s hs => modelRepCorrectedHarchPackage_split
              ZF 1 (by norm_num) s hs)
            h_genuine_poles))) :
    RiemannHypothesis := by
  exact
    RH_from_model_corrected
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
      (by rfl)
      normalFormGroupedLayer

#print axioms realPrime_RH_model_corrected

end
end RHFormalization
