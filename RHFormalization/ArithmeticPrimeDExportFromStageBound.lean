import RHFormalization.ArithmeticPrimeResidualWitnessBridge

/-!
# ArithmeticPrimeDExportFromStageBound

This file proves the clean reduction:

  a bound on the real Appendix-D witness remainder R_stage
  implies the honest arithmetic prime D.EXPORT statement.

This is the exact theorem that converts the analytic Appendix-D estimate into
the formal D-side export for the real arithmetic prime operator.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/--
If the Appendix-D witness remainder is bounded on `K`, then the arithmetic
prime operator satisfies the honest D.EXPORT residual bound against the witness
`B_stage`.

This is the formal reduction from the analytic `R_stage` estimate to
`ArithmeticPrimeDExport`.
-/
theorem ArithmeticPrimeDExport_of_stageField_R_stage_bound
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (K : Set ℂ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hR :
      ∀ s ∈ K,
        ‖stageFieldSpikeExtractionWitness.R_stage
          (arithmeticPrimeOperatorDFiniteStage n μ M hnn)
          s‖ ≤ C) :
    ArithmeticPrimeDExport n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      K := by
  unfold ArithmeticPrimeDExport
  unfold PerturbedDExport
  refine ⟨C, hC, ?_⟩
  intro s hs
  rw [← arithmeticPrimeResidual_eq_perturbedResidual
      (N := N)
      n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      s]
  rw [arithmeticPrimeResidual_eq_stageField_R_stage
      (N := N) n μ M hnn s]
  exact hR s hs

#print axioms ArithmeticPrimeDExport_of_stageField_R_stage_bound

end

end RHFormalization
