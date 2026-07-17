import RHFormalization.ArithmeticPrimeDExportFromKernelBounds
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel

/-!
# ArithmeticPrimeActualKernelBound

This file instantiates the abstract kernel-bound reduction with the actual
Appendix-D witness kernel:

  displacementCanonicalKernel (heatKernelG 1)

The kernel is displacement-only, so its norm is bounded by the exact majorant

  displacementKernelMajorant (heatKernelG 1) q.

This is still fixed-stage/off-real-axis. It removes the abstract `kernelBound`
hypothesis from the B-side.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
The actual witness spike kernel is bounded by the displacement majorant attached
to its decoded prime-power index.
-/
theorem stageField_spikeKernel_bound_by_displacement_majorant
    (α : DFiniteStage)
    (q : ℕ)
    (s : ℂ) :
    ‖stageFieldSpikeExtractionWitness.spikeKernel α q s‖ ≤
      displacementKernelMajorant
        (heatKernelG (1 : ℝ))
        (stageFieldSpikeExtractionWitness.toPP α q) := by
  unfold AppendixDFiniteSpikeExtractionWitness.spikeKernel
  unfold AppendixDFiniteSpikeExtractionWitness.Kcan
  unfold displacementCanonicalKernel
  unfold displacementKernelMajorant
  rfl

/--
The actual displacement-kernel majorant is nonnegative.
-/
theorem stageField_displacement_kernelBound_nonneg
    (α : DFiniteStage) :
    ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices α,
      0 ≤
        displacementKernelMajorant
          (heatKernelG (1 : ℝ))
          (stageFieldSpikeExtractionWitness.toPP α q) := by
  intro q hq
  exact displacementKernelMajorant_nonneg (heatKernelG (1 : ℝ))
    (stageFieldSpikeExtractionWitness.toPP α q)

/--
Fixed-stage ArithmeticPrimeDExport with the actual displacement kernel.

Inputs left:
* `δ ≤ |Im s|` for the F-stage off-real-axis bound;
* the honest shift/nonnegativity hypothesis `hnn`.

No abstract B-term or kernel-bound hypotheses remain.
-/
theorem ArithmeticPrimeDExport_fixedStage_of_im_lower_actual_kernel
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
    (hK : ∀ s ∈ K, δ ≤ |Complex.im s|) :
    ArithmeticPrimeDExport n μ
      (stageFieldSpikeExtractionWitness.B_stage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      K := by
  let α := arithmeticPrimeOperatorDFiniteStage n μ M hnn
  exact
    ArithmeticPrimeDExport_fixedStage_of_im_lower_and_kernel_bounds
      n μ M hnn K δ hδ hK
      (fun q =>
        displacementKernelMajorant
          (heatKernelG (1 : ℝ))
          (stageFieldSpikeExtractionWitness.toPP α q))
      (by
        intro q hq
        exact stageField_displacement_kernelBound_nonneg α q hq)
      (by
        intro s hs q hq
        exact stageField_spikeKernel_bound_by_displacement_majorant α q s)

#print axioms stageField_spikeKernel_bound_by_displacement_majorant
#print axioms stageField_displacement_kernelBound_nonneg
#print axioms ArithmeticPrimeDExport_fixedStage_of_im_lower_actual_kernel

end

end RHFormalization
