import RHFormalization.ArithmeticPrimeDExportFixedStage

/-!
# ArithmeticPrimeDExportFromKernelBounds

This file removes the abstract `termBound` layer.

It shows that if every active spike kernel is bounded on `K` by `kernelBound q`,
then the finite B-stage term bound follows automatically, and therefore the
fixed-stage arithmetic prime D.EXPORT theorem follows.

This is still fixed-stage. The next step after this is to instantiate
`kernelBound` using the actual canonical kernel estimates.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
B-stage bound from kernel bounds.

If each active kernel is bounded by `kernelBound q` on `K`, then the B-stage is
bounded by the finite sum of coefficient norms times those kernel bounds.
-/
theorem stageField_B_stage_bound_on_K_of_kernel_bounds
    (α : DFiniteStage)
    (Kset : Set ℂ)
    (kernelBound : ℕ → ℝ)
    (hkernel_nonneg :
      ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices α,
        0 ≤ kernelBound q)
    (hkernel :
      ∀ s ∈ Kset,
        ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices α,
          ‖stageFieldSpikeExtractionWitness.spikeKernel α q s‖
            ≤ kernelBound q) :
    ∀ s ∈ Kset,
      ‖stageFieldSpikeExtractionWitness.B_stage α s‖ ≤
        (stageFieldSpikeExtractionWitness.activeIndices α).sum
          (fun q => ‖α.diagonalSpikeContribution q‖ * kernelBound q) := by
  exact
    stageField_B_stage_bound_on_K_of_term_bounds
      α
      Kset
      (fun q => ‖α.diagonalSpikeContribution q‖ * kernelBound q)
      (by
        intro s hs q hq
        exact mul_le_mul_of_nonneg_left
          (hkernel s hs q hq)
          (norm_nonneg _))

/--
Fixed-stage arithmetic D.EXPORT from:
1. imaginary-axis separation for the F-stage;
2. kernel bounds for the B-stage.

This is the cleaner fixed-stage theorem we need before replacing the
`|Im s|` condition by the real Ω-compact distance condition.
-/
theorem ArithmeticPrimeDExport_fixedStage_of_im_lower_and_kernel_bounds
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
    (kernelBound : ℕ → ℝ)
    (hkernel_nonneg :
      ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn),
        0 ≤ kernelBound q)
    (hkernel :
      ∀ s ∈ K,
        ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices
          (arithmeticPrimeOperatorDFiniteStage n μ M hnn),
          ‖stageFieldSpikeExtractionWitness.spikeKernel
              (arithmeticPrimeOperatorDFiniteStage n μ M hnn) q s‖
            ≤ kernelBound q) :
    ArithmeticPrimeDExport n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      K := by
  exact
    ArithmeticPrimeDExport_fixedStage_of_im_lower_and_B_terms
      n μ M hnn K δ hδ hK
      (fun q =>
        ‖(arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeContribution q‖ *
          kernelBound q)
      (by
        intro q hq
        exact mul_nonneg (norm_nonneg _) (hkernel_nonneg q hq))
      (by
        intro s hs q hq
        exact mul_le_mul_of_nonneg_left
          (hkernel s hs q hq)
          (norm_nonneg _))

#print axioms stageField_B_stage_bound_on_K_of_kernel_bounds
#print axioms ArithmeticPrimeDExport_fixedStage_of_im_lower_and_kernel_bounds

end

end RHFormalization
