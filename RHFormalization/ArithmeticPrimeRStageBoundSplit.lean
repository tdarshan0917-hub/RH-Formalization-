import RHFormalization.ArithmeticPrimeDExportFromStageBound

/-!
# ArithmeticPrimeRStageBoundSplit

This file proves the next clean reduction:

  F-stage bound + B-stage bound
  ⇒ R-stage bound
  ⇒ ArithmeticPrimeDExport.

This exposes the remaining analytic work:
  1. bound the arithmetic prime resolvent F-stage;
  2. bound the finite canonical spike B-stage.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/--
If the arithmetic prime F-stage and the witness B-stage are bounded on `K`,
then the witness remainder `R_stage = F_stage - B_stage` is bounded on `K`.
-/
theorem stageField_R_stage_bound_of_F_B_bounds
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (K : Set ℂ)
    (CF CB : ℝ)
    (hCF : 0 ≤ CF)
    (hCB : 0 ≤ CB)
    (hF :
      ∀ s ∈ K,
        ‖arithmeticPrimeFStage n μ s‖ ≤ CF)
    (hB :
      ∀ s ∈ K,
        ‖stageFieldSpikeExtractionWitness.B_stage
          (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
          s‖ ≤ CB) :
    ∀ s ∈ K,
      ‖stageFieldSpikeExtractionWitness.R_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
        s‖ ≤ CF + CB := by
  intro s hs
  unfold AppendixDFiniteSpikeExtractionWitness.R_stage
  rw [stageFieldWitness_arithmetic_F_stage n μ M hnn]
  calc
    ‖primePerturbedFStage μ (primeStageWeights n) s
      -
      stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
        s‖
        ≤ ‖primePerturbedFStage μ (primeStageWeights n) s‖
          +
          ‖stageFieldSpikeExtractionWitness.B_stage
            (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
            s‖ := by
            simpa [sub_eq_add_neg, norm_neg] using
              norm_add_le
                (primePerturbedFStage μ (primeStageWeights n) s)
                (-
                  stageFieldSpikeExtractionWitness.B_stage
                    (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
                    s)
    _ ≤ CF + CB := add_le_add (hF s hs) (hB s hs)

/--
F-bound + B-bound imply the honest arithmetic D.EXPORT statement.
-/
theorem ArithmeticPrimeDExport_of_F_B_bounds
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (K : Set ℂ)
    (CF CB : ℝ)
    (hCF : 0 ≤ CF)
    (hCB : 0 ≤ CB)
    (hF :
      ∀ s ∈ K,
        ‖arithmeticPrimeFStage n μ s‖ ≤ CF)
    (hB :
      ∀ s ∈ K,
        ‖stageFieldSpikeExtractionWitness.B_stage
          (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
          s‖ ≤ CB) :
    ArithmeticPrimeDExport n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      K := by
  exact ArithmeticPrimeDExport_of_stageField_R_stage_bound
    n μ M hnn K (CF + CB) (add_nonneg hCF hCB)
    (stageField_R_stage_bound_of_F_B_bounds
      n μ M hnn K CF CB hCF hCB hF hB)

#print axioms stageField_R_stage_bound_of_F_B_bounds
#print axioms ArithmeticPrimeDExport_of_F_B_bounds

end

end RHFormalization
