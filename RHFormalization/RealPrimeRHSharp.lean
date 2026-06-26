import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.PrimePerturbedOperatorLayerAligned
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/-- RH on the REAL prime layer via the sharp assembly RH_from_raw_inputs.
finiteOperatorLayer = primePerturbedOperatorLayerAligned μ (NOT designedY).
Builds the real Y inline; zero side built inline. Remaining = raw data inputs. -/
theorem realPrime_RH_sharp
    (μ : Fin N → ℝ)
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
          (primePerturbedOperatorLayerAligned μ))
    (F : DFHLimitData (primePerturbedOperatorLayerAligned μ).toStagePackage)
    (R : DMasterResidualData (primePerturbedOperatorLayerAligned μ).toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ (primePerturbedOperatorLayerAligned μ).toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha)
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le :
      (SharpCutoffChosenLengthSharedPackage (primePerturbedOperatorLayerAligned μ) S).sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        (SharpCutoffChosenLengthSharedPackage (primePerturbedOperatorLayerAligned μ) S).Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis :=
  RH_from_raw_inputs h_real_zero_free
    (primePerturbedOperatorLayerAligned μ) S F R h_R_stage_bound hσ hF_alpha hR_alpha
    M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
    sigmaH h_C_sigma_le h_split h_pp

#print axioms realPrime_RH_sharp

end
end RHFormalization
