import RHFormalization.ArithmeticShiftedLaplaceBStageFiniteCanonical

/-!
# ArithmeticShiftedLaplaceBStageConcrete

Concrete cutoff-index version of the clean shifted-Laplace B-stage connector.

This strengthens the previous image-index theorem to the actual concrete
prime-power cutoff enumeration:

  concretePrimePowerBelowCutoff ((n : ℝ) + 1)

This is the exact finite package shape needed for the existing shifted-Laplace
finite-package convergence machinery.

No designedSpikeWitness.
No stageFieldSpikeExtractionWitness.
No displacement kernel.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
The decoded image of the active Nat stage codes is exactly the concrete
prime-power cutoff set.
-/
theorem ppStageCodes_image_ppDecode_eq_concretePrimePowerBelowCutoff
    (n : ℕ) :
    (ppStageCodes n).image ppDecode =
      concretePrimePowerBelowCutoff ((n : ℝ) + 1) := by
  rw [ppStageCodes, Finset.image_image]
  simp [Function.comp_def, ppDecode_ppCode]

/--
The corrected arithmetic shifted-Laplace B-stage is exactly the finite canonical
prime-power package over the concrete cutoff enumeration.
-/
theorem arithmeticPrimeShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_concrete
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
        (concretePrimePowerBelowCutoff ((n : ℝ) + 1))
        shiftedLaplaceHeatKernelC
        s := by
  rw [arithmeticPrimeShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image]
  have hidx :
      ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices.image
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP)
        =
      concretePrimePowerBelowCutoff ((n : ℝ) + 1) := by
    simpa [arithmeticPrimeOperatorDFiniteStage, primeOperatorDFiniteStage, primePowerStage]
      using ppStageCodes_image_ppDecode_eq_concretePrimePowerBelowCutoff n
  rw [hidx]

#print axioms ppStageCodes_image_ppDecode_eq_concretePrimePowerBelowCutoff
#print axioms arithmeticPrimeShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_concrete

end

end RHFormalization
