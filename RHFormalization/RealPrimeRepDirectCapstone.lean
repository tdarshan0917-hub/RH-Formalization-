import RHFormalization.ShiftedLaplaceRepDirectEndpoint
import RHFormalization.RealPrimeRepCorrectedCapstone
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/--
Real-prime capstone through the direct corrected Rep H-side.

This is the corrected replacement for the older Rep capstone path that still
carried the generic `ZeroPoleLocalUniformConvergenceAPI` slot.
-/
theorem realPrime_RH_rep_direct
    {N : ℕ}
    (μ : Fin N → ℝ)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
          (primePerturbedOperatorLayerAligned μ))
    (FH RH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_F_stage_to_FH :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            ∀ s ∈ K,
              dist
                ((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage
                  (S.alpha n) s)
                (FH s) < ε)
    (h_R_stage_to_RH :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            ∀ s ∈ K,
              dist
                ((primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                  (S.alpha n) s)
                (RH s) < ε)
    (h_R_stage_bound :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ α : DFiniteStage, ∀ s ∈ K,
            ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ (primePerturbedOperatorLayerAligned μ).toStagePackage.sigma0)
    (ZF : ZetaZeroFacts)
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ))
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z)
    (hYC :
      (realPrimeY μ S FH RH
        h_FH_holo h_RH_holo
        h_F_stage_to_FH h_R_stage_to_RH
        h_R_stage_bound hσ).B.Cshared =
        shiftedLaplacePrimePackageAt 1)
    (M :
      MeromorphicIdentityTheoremAPI
        (realPrimeY μ S FH RH
          h_FH_holo h_RH_holo
          h_F_stage_to_FH h_R_stage_to_RH
          h_R_stage_bound hσ).toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        (shiftedLaplaceRepInterfaceBridge
          ZF
          (realPrimeY μ S FH RH
            h_FH_holo h_RH_holo
            h_F_stage_to_FH h_R_stage_to_RH
            h_R_stage_bound hσ)
          hbridge hB_regular hYC))
    (Pobs :
      LocalPoleObstructionAPI
        (realPrimeY μ S FH RH
          h_FH_holo h_RH_holo
          h_F_stage_to_FH h_R_stage_to_RH
          h_R_stage_bound hσ).toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        (shiftedLaplaceRepInterfaceBridge
          ZF
          (realPrimeY μ S FH RH
            h_FH_holo h_RH_holo
            h_F_stage_to_FH h_R_stage_to_RH
            h_R_stage_bound hσ)
          hbridge hB_regular hYC)) :
    RiemannHypothesis :=
  RH_from_direct_corrected_rep_shared
    ZF
    (realPrimeY μ S FH RH
      h_FH_holo h_RH_holo
      h_F_stage_to_FH h_R_stage_to_RH
      h_R_stage_bound hσ)
    hbridge
    hB_regular
    hYC
    M
    Pobs

#print axioms realPrime_RH_rep_direct

end
end RHFormalization
