import RHFormalization.ArithmeticPrimeOperatorResidual
import RHFormalization.AppendixDFiniteSpikeExtractionWitness

/-!
# ArithmeticPrimeResidualWitnessBridge

This file connects the arithmetic prime operator residual to the existing
Appendix-D finite spike extraction witness machinery.

Goal:
  arithmeticPrimeResidual = W.R_stage

for the witness W built directly from DFiniteStage fields.

This is still algebraic. The next hard theorem is the bound on W.R_stage.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/--
Canonical witness built directly from the fields already stored in `DFiniteStage`.

This avoids fake/empty witnesses: it uses each stage's own active indices,
prime-power decoding, coefficient compatibility, and actual `appendixDFiniteFStage`.
-/
noncomputable def stageFieldSpikeExtractionWitness :
    AppendixDFiniteSpikeExtractionWitness :=
  { F_stage := fun α => α.appendixDFiniteFStage
    activeIndices := fun α => α.diagonalSpikeActiveIndices
    h_activeIndices_active := by
      intro α q hq
      exact α.h_diagonalSpikeActiveIndices_active q hq
    h_activeIndices_complete := by
      intro α q hq
      exact α.h_diagonalSpikeActiveIndices_complete q hq
    toPP := fun α => α.diagonalSpikeToPP
    hinj := by
      intro α m hm n hn h
      exact α.h_diagonalSpikeToPP_inj m hm n hn h
    hcoeff := by
      intro α n hn
      exact α.h_canonicalSpikeContribution_eq_weightC n hn }

/--
For the arithmetic prime operator stage, the witness F-stage is the real
prime-perturbed F-stage.
-/
theorem stageFieldWitness_arithmetic_F_stage
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y))) :
    stageFieldSpikeExtractionWitness.F_stage
      (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
      =
      primePerturbedFStage μ (primeStageWeights n) := by
  exact arithmeticPrimeOperatorDFiniteStage_F_stage n μ M hnn

/--
The arithmetic prime residual against the witness B-stage is exactly the
Appendix-D witness remainder `R_stage`.

This is the clean algebraic bridge to the real D-side bound.
-/
theorem arithmeticPrimeResidual_eq_stageField_R_stage
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (s : ℂ) :
    arithmeticPrimeResidual n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      s
    =
    stageFieldSpikeExtractionWitness.R_stage
      (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
      s := by
  unfold arithmeticPrimeResidual arithmeticPrimeFStage
  unfold AppendixDFiniteSpikeExtractionWitness.R_stage
  rw [stageFieldWitness_arithmetic_F_stage n μ M hnn]

#print axioms stageFieldSpikeExtractionWitness
#print axioms stageFieldWitness_arithmetic_F_stage
#print axioms arithmeticPrimeResidual_eq_stageField_R_stage

end

end RHFormalization
