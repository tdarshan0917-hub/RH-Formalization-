import RHFormalization.ArithmeticShiftedPrimeDExportFromHnn

/-!
# ArithmeticShiftedLaplaceBStageFiniteCanonical

Connector theorem for the next phase.

This identifies the clean arithmetic shifted-Laplace finite B-stage with the
canonical finite prime-power package over the decoded active prime-power indices.

This is the bridge needed before using the existing shifted-Laplace convergence
machinery to pass from finite stages to Bshared/Bcan.

No designedSpikeWitness.
No stageFieldSpikeExtractionWitness.
No displacement kernel.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
Generic connector: the clean shifted-Laplace B-stage of any `DFiniteStage`
is the finite canonical prime-power package over the decoded active indices.
-/
theorem arithmeticShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image
    (α : DFiniteStage)
    (s : ℂ) :
    arithmeticShiftedLaplaceBStage α s =
      finiteCanonicalPrimePowerPackage
        (α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP)
        shiftedLaplaceHeatKernelC
        s := by
  unfold arithmeticShiftedLaplaceBStage
  unfold finiteNatSpikePackage
  unfold finiteCanonicalPrimePowerPackage
  unfold arithmeticShiftedLaplaceSpikeKernel

  -- Rewrite the canonical sum over the image back to a Nat-indexed sum.
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro q hq

    have hactive : α.diagonalSpikeActive q :=
      α.h_diagonalSpikeActiveIndices_active q hq

    have hdiag :
        α.diagonalSpikeContribution q =
          α.canonicalSpikeContribution q :=
      α.h_diagonalSpikeExtraction q hactive

    have hcanon :
        α.canonicalSpikeContribution q =
          PrimePowerPair.weightC (α.diagonalSpikeToPP q) :=
      α.h_canonicalSpikeContribution_eq_weightC q hq

    rw [hdiag, hcanon]
  · intro a ha b hb hab
    exact α.h_diagonalSpikeToPP_inj a ha b hb hab

/--
Specialized connector for the corrected arithmetic prime-operator stage.
-/
theorem arithmeticPrimeShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights (N := N) n) M y)))
    (s : ℂ) :
    arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn) s =
      finiteCanonicalPrimePowerPackage
        ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices.image
          (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP)
        shiftedLaplaceHeatKernelC
        s := by
  exact arithmeticShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image
    (arithmeticPrimeOperatorDFiniteStage n μ M hnn) s

#print axioms arithmeticShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image
#print axioms arithmeticPrimeShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image

end

end RHFormalization
