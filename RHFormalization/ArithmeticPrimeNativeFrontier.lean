-- SENTINEL: native-frontier-v1
import RHFormalization.ArithmeticPrimeCoScaledNet
import RHFormalization.ArithmeticPrimeResidualWitnessBridge
import RHFormalization.DMasterResidualAlong
import Mathlib

/-!
# ArithmeticPrimeNativeFrontier — D.MR data along the co-scaled net
Package fields read the STAGE'S OWN F (native witness, PKG2a), not any
fixed-N payload formula. Applying buildDMasterResidualDataAlong at
arithmeticPrimeNet freezes THE FRONTIER in the kernel:
  CONDITIONAL package assembly along the co-scaled net. Proves NO estimates:
  records the exact h_stage_holo + h_conv interface of buildDMasterResidualDataAlong.
  h_conv is the main theorem; producers for Nfun/mu/M/hnn and the RH consumer
  are separate obligations (roadmap 2026-07-16F).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- Native package: F/B/R from the stage-field witness. σ₀ = 1. -/
noncomputable def arithmeticPrimeNativePackage : DFiniteStagePackage :=
  { F_stage := stageFieldSpikeExtractionWitness.F_stage
    B_stage := stageFieldSpikeExtractionWitness.B_stage
    R_stage := stageFieldSpikeExtractionWitness.R_stage
    sigma0 := 1 }

/-- **THE FROZEN FRONTIER.** D.MR data for the native package along the
co-scaled arithmetic prime net, from stage-holo + h_conv. -/
noncomputable def arithmeticPrimeNet_DMasterResidual
    (Nfun : ℕ → ℕ) (μ : ∀ n, Fin (Nfun n) → ℝ) (M : ℝ)
    (hnn : ∀ n : ℕ, ∀ y : EuclideanSpace ℂ (Fin (Nfun n)),
      0 ≤ RCLike.re (inner ℂ y
        (primeOpCLM (μ n) (primeStageWeights (N := Nfun n) n) M y)))
    (R_H : ℂ → ℂ)
    (h_stage_holo : ∀ n : ℕ,
      HolomorphicOnC
        (fun s => arithmeticPrimeNativePackage.R_stage
          (arithmeticPrimeNet Nfun μ M hnn n) s) Ω)
    (h_conv :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
            dist (arithmeticPrimeNativePackage.R_stage
              (arithmeticPrimeNet Nfun μ M hnn n) s) (R_H s) < ε) :
    DMasterResidualData arithmeticPrimeNativePackage :=
  buildDMasterResidualDataAlong
    arithmeticPrimeNativePackage
    (arithmeticPrimeNet Nfun μ M hnn)
    R_H h_stage_holo h_conv

#print axioms arithmeticPrimeNativePackage
#print axioms arithmeticPrimeNet_DMasterResidual

end

end RHFormalization
