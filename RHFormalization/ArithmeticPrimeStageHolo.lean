import RHFormalization.ArithmeticPrimeResidualWitnessBridge
import RHFormalization.PrimePerturbedFStage
import RHFormalization.AppendixDSpikeSumExtraction
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import Mathlib

/-!
# Stage holomorphy along the arithmetic-prime route

`R_stage = F_stage - B_stage` holomorphic on Ω for the genuine prime stage:
F = primePerturbedFStage (holo via primePerturbedFStage_holo, given nonneg spectrum);
B = finite spike sum, s-independent kernel, hence holo. Discharges h_stage_holo (input 1)
of buildDMasterResidualDataAlong for a non-degenerate capstone-connected stage.
-/

namespace RHFormalization
noncomputable section
open Complex

/-- **Stage holomorphy for the arithmetic-prime stage.** -/
theorem stageField_R_stage_holo_arithmetic
    {N : ℕ} (n : ℕ) (μ : Fin N → ℝ) (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (hpos :
      ∀ i, 0 ≤ perturbedEigenvalues μ
              (primePotential_isHermitian (primeStageWeights n)) i) :
    HolomorphicOnC
      (fun s => stageFieldSpikeExtractionWitness.R_stage
                  (arithmeticPrimeOperatorDFiniteStage n μ M hnn) s) Ω := by
  set α := arithmeticPrimeOperatorDFiniteStage n μ M hnn with hα
  have hsplit :
      (fun s => stageFieldSpikeExtractionWitness.R_stage α s)
        = (fun s => stageFieldSpikeExtractionWitness.F_stage α s)
            - (fun s => stageFieldSpikeExtractionWitness.B_stage α s) := by
    funext s
    rfl
  rw [hsplit]
  have hF : HolomorphicOnC (fun s => stageFieldSpikeExtractionWitness.F_stage α s) Ω := by
    have hEq : (fun s => stageFieldSpikeExtractionWitness.F_stage α s)
            = primePerturbedFStage μ (primeStageWeights n) := by
      rw [hα]
      exact stageFieldWitness_arithmetic_F_stage n μ M hnn
    rw [hEq]
    exact primePerturbedFStage_holo μ (primeStageWeights n) hpos
  -- B is genuinely s-constant: the canonical kernel discards s
  -- (`displacementCanonicalKernel G = fun a _s => G a`), so the whole finite sum
  -- is constant in s, hence holomorphic.
  have hB : HolomorphicOnC (fun s => stageFieldSpikeExtractionWitness.B_stage α s) Ω := by
    have hBconst :
        (fun s => stageFieldSpikeExtractionWitness.B_stage α s)
          = (fun _ : ℂ => stageFieldSpikeExtractionWitness.B_stage α 0) := by
      funext s
      show finiteNatSpikePackage
            (stageFieldSpikeExtractionWitness.activeIndices α)
            α.diagonalSpikeContribution
            (stageFieldSpikeExtractionWitness.spikeKernel α) s
          = finiteNatSpikePackage
            (stageFieldSpikeExtractionWitness.activeIndices α)
            α.diagonalSpikeContribution
            (stageFieldSpikeExtractionWitness.spikeKernel α) 0
      unfold finiteNatSpikePackage
      refine Finset.sum_congr rfl ?_
      intro q hq
      simp only [AppendixDFiniteSpikeExtractionWitness.spikeKernel,
        AppendixDFiniteSpikeExtractionWitness.Kcan,
        displacementCanonicalKernel]
    rw [hBconst]
    exact analyticOn_const
  exact hF.sub hB

#print axioms stageField_R_stage_holo_arithmetic

end
end RHFormalization
