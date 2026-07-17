import RHFormalization.ArithmeticPrimeBStageBound

/-!
# ArithmeticPrimeDExportFixedStage

This file combines the already-proven F-stage bound and B-stage finite-sum
bound into a usable fixed-stage `ArithmeticPrimeDExport`.

This is still fixed-stage/off-real-axis. It is not the final cutoff-uniform
Appendix-D theorem.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
Fixed-stage D.EXPORT from:
1. a uniform imaginary-axis lower bound on `K`;
2. finite termwise bounds for the witness B-stage.

This packages the current fixed-stage result.
-/
theorem ArithmeticPrimeDExport_fixedStage_of_im_lower_and_B_terms
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (K : Set ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hK : ∀ s ∈ K, δ ≤ |Complex.im s|)
    (termBound : ℕ → ℝ)
    (hterm_nonneg :
      ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn),
        0 ≤ termBound q)
    (hterm :
      ∀ s ∈ K,
        ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices
          (arithmeticPrimeOperatorDFiniteStage n μ M hnn),
          ‖(arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeContribution q‖ *
          ‖stageFieldSpikeExtractionWitness.spikeKernel
              (arithmeticPrimeOperatorDFiniteStage n μ M hnn) q s‖
            ≤ termBound q) :
    ArithmeticPrimeDExport n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      K := by
  let α := arithmeticPrimeOperatorDFiniteStage n μ M hnn
  let CF : ℝ := (N : ℝ) / δ
  let CB : ℝ := (stageFieldSpikeExtractionWitness.activeIndices α).sum termBound

  have hCF : 0 ≤ CF := by
    unfold CF
    exact div_nonneg (by exact_mod_cast Nat.zero_le N) (le_of_lt hδ)

  have hCB : 0 ≤ CB := by
    unfold CB
    apply Finset.sum_nonneg
    intro q hq
    exact hterm_nonneg q hq

  have hF :
      ∀ s ∈ K,
        ‖arithmeticPrimeFStage n μ s‖ ≤ CF := by
    unfold CF
    exact arithmeticPrimeFStage_bound_on_K_of_im_lower n μ K δ hδ hK

  have hB :
      ∀ s ∈ K,
        ‖stageFieldSpikeExtractionWitness.B_stage α s‖ ≤ CB := by
    unfold CB
    exact stageField_B_stage_bound_on_K_of_term_bounds α K termBound hterm

  exact ArithmeticPrimeDExport_of_F_B_bounds
    n μ M hnn K CF CB hCF hCB hF hB

#print axioms ArithmeticPrimeDExport_fixedStage_of_im_lower_and_B_terms

end

end RHFormalization
