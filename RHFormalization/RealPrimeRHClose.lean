import RHFormalization.OmegaPuncturedIdentityEndpoint
import RHFormalization.RealPrimeY
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/-- RH close on the real prime layer: mainTheorem applied to realPrimeY + the four
structural inputs. Remaining inputs (ZF, X, E, OIP) + realPrimeY's own inputs named. -/
theorem realPrime_RH
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
    (ZF : ZetaZeroFacts)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
          (realPrimeY μ S FH RH h_FH_holo h_RH_holo h_F_stage_to_FH h_R_stage_to_RH h_R_stage_bound hσ).toOperatorResolventBridge
          X.toLegacyZeroPolePackageAPI)
    (OIP : OmegaPuncturedMeromorphicIdentityAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_omegaPuncturedIdentity
    ZF
    (realPrimeY μ S FH RH h_FH_holo h_RH_holo h_F_stage_to_FH h_R_stage_to_RH h_R_stage_bound hσ)
    X
    E
    OIP

#print axioms realPrime_RH

end
end RHFormalization
