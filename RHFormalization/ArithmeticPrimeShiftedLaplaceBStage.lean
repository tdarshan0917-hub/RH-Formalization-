import RHFormalization.ArithmeticPrimeGenericDExportBounds
import RHFormalization.ArithmeticPrimeBStageBound
import RHFormalization.ShiftedLaplaceKernelPatchBound
import RHFormalization.AppendixDSpikeSumExtraction

/-!
# ArithmeticPrimeShiftedLaplaceBStage

This file fixes the kernel route.

It does NOT use `stageFieldSpikeExtractionWitness.Kcan`, because that path is
hardcoded to the displacement kernel.

Instead it defines the B-stage directly from the arithmetic DFiniteStage fields
and the live shifted-Laplace kernel:

  shiftedLaplaceHeatKernelC.

This is the correct B-side object for the shifted-Laplace/Stieltjes endgame.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/-- Live shifted-Laplace spike kernel built directly from a DFiniteStage. -/
noncomputable def arithmeticShiftedLaplaceSpikeKernel
    (α : DFiniteStage) : ℕ → ℂ → ℂ :=
  fun q s =>
    shiftedLaplaceHeatKernelC
      (PrimePowerPair.center (α.diagonalSpikeToPP q))
      s

/-- Live shifted-Laplace B-stage built directly from the arithmetic DFiniteStage fields. -/
noncomputable def arithmeticShiftedLaplaceBStage
    (α : DFiniteStage) : ℂ → ℂ :=
  finiteNatSpikePackage
    α.diagonalSpikeActiveIndices
    α.diagonalSpikeContribution
    (arithmeticShiftedLaplaceSpikeKernel α)

/-- Definitional expansion of the live shifted-Laplace B-stage. -/
theorem arithmeticShiftedLaplaceBStage_eq_finiteNatSpikePackage
    (α : DFiniteStage) (s : ℂ) :
    arithmeticShiftedLaplaceBStage α s =
      finiteNatSpikePackage
        α.diagonalSpikeActiveIndices
        α.diagonalSpikeContribution
        (arithmeticShiftedLaplaceSpikeKernel α)
        s := by
  rfl

/--
Finite-stage bound for the live shifted-Laplace B-stage.

Inputs:
* active centers are nonnegative;
* `sqrt(s+1/4).re` is uniformly at least `sigma` on K.

This uses the actual shifted-Laplace kernel bound, not the displacement kernel.
-/
theorem arithmeticShiftedLaplaceBStage_bound_on_K_of_region
    (α : DFiniteStage)
    (Kset : Set ℂ)
    (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hcenter :
      ∀ q ∈ α.diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center (α.diagonalSpikeToPP q))
    (hregion :
      ∀ s ∈ Kset,
        sigma ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ∀ s ∈ Kset,
      ‖arithmeticShiftedLaplaceBStage α s‖ ≤
        α.diagonalSpikeActiveIndices.sum
          (fun q =>
            ‖α.diagonalSpikeContribution q‖ *
              ((1 / (2 * sigma)) *
                Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma))) := by
  intro s hs
  calc
    ‖arithmeticShiftedLaplaceBStage α s‖
        ≤ α.diagonalSpikeActiveIndices.sum
            (fun q =>
              ‖α.diagonalSpikeContribution q‖ *
                ‖arithmeticShiftedLaplaceSpikeKernel α q s‖) := by
          simpa [arithmeticShiftedLaplaceBStage,
                 arithmeticShiftedLaplaceSpikeKernel] using
            finiteNatSpikePackage_norm_le_sum
              α.diagonalSpikeActiveIndices
              α.diagonalSpikeContribution
              (arithmeticShiftedLaplaceSpikeKernel α)
              s
    _ ≤ α.diagonalSpikeActiveIndices.sum
          (fun q =>
            ‖α.diagonalSpikeContribution q‖ *
              ((1 / (2 * sigma)) *
                Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma))) := by
          apply Finset.sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left
          · unfold arithmeticShiftedLaplaceSpikeKernel
            exact shiftedLaplace_kernel_norm_le_of_re_ge
              (PrimePowerPair.center (α.diagonalSpikeToPP q))
              (hcenter q hq)
              sigma
              hsigma
              s
              (hregion s hs)
          · exact norm_nonneg _

/--
Live shifted-Laplace fixed-stage D.EXPORT.

This is the corrected theorem: it uses the arithmetic prime F-stage and the live
shifted-Laplace B-stage, not the displacement witness.
-/
theorem ArithmeticPrimeDExport_of_im_lower_shiftedLaplaceBStage
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (Kset : Set ℂ)
    (delta sigma : ℝ)
    (hdelta : 0 < delta)
    (hK_im : ∀ s ∈ Kset, delta ≤ |Complex.im s|)
    (hsigma : 0 < sigma)
    (hcenter :
      ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center
          ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q))
    (hregion :
      ∀ s ∈ Kset,
        sigma ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ArithmeticPrimeDExport n μ
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      Kset := by
  let α := arithmeticPrimeOperatorDFiniteStage n μ M hnn
  let CB : ℝ :=
    α.diagonalSpikeActiveIndices.sum
      (fun q =>
        ‖α.diagonalSpikeContribution q‖ *
          ((1 / (2 * sigma)) *
            Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma)))
  have hCB : 0 ≤ CB := by
    unfold CB
    apply Finset.sum_nonneg
    intro q hq
    apply mul_nonneg
    · exact norm_nonneg _
    · apply mul_nonneg
      · positivity
      · exact Real.exp_nonneg _
  have hB :
      ∀ s ∈ Kset,
        ‖arithmeticShiftedLaplaceBStage α s‖ ≤ CB := by
    unfold CB
    exact arithmeticShiftedLaplaceBStage_bound_on_K_of_region
      α Kset sigma hsigma hcenter hregion
  exact ArithmeticPrimeDExport_of_im_lower_and_generic_B_bound
    n μ
    (arithmeticShiftedLaplaceBStage α)
    Kset
    delta
    hdelta
    hK_im
    CB
    hCB
    hB

#print axioms arithmeticShiftedLaplaceSpikeKernel
#print axioms arithmeticShiftedLaplaceBStage
#print axioms arithmeticShiftedLaplaceBStage_bound_on_K_of_region
#print axioms ArithmeticPrimeDExport_of_im_lower_shiftedLaplaceBStage

end

end RHFormalization
