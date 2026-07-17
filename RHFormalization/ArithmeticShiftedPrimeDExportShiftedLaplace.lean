import RHFormalization.ArithmeticShiftedPrimeFStageBound

/-!
# ArithmeticShiftedPrimeDExportShiftedLaplace

Corrected fixed-stage D.EXPORT:

* shifted arithmetic prime F-stage, aligned with the shifted native operator;
* live shifted-Laplace B-stage;
* denominator gap from the shifted spectrum;
* shifted-Laplace region bound.

This is the corrected finite-stage theorem: no displacement kernel, no unshifted
F-stage.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
Corrected fixed-stage D.EXPORT with shifted F-stage and live shifted-Laplace B-stage.
-/
theorem ArithmeticShiftedPrimeDExport_of_spectral_gap_shiftedLaplaceBStage
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (Kset : Set ℂ)
    (δ sigma : ℝ)
    (hδ : 0 < δ)
    (hgap :
      ∀ s ∈ Kset,
        ∀ i : Fin N,
          δ ≤ ‖s +
            ((perturbedEigenvalues
              (μShift μ M)
              (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖)
    (hsigma : 0 < sigma)
    (hcenter :
      ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center
          ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q))
    (hregion :
      ∀ s ∈ Kset,
        sigma ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    PerturbedDExport
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      Kset := by
  let α := arithmeticPrimeOperatorDFiniteStage n μ M hnn
  let CF : ℝ := (N : ℝ) / δ
  let CB : ℝ :=
    α.diagonalSpikeActiveIndices.sum
      (fun q =>
        ‖α.diagonalSpikeContribution q‖ *
          ((1 / (2 * sigma)) *
            Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma)))

  have hCF : 0 ≤ CF := by
    unfold CF
    exact div_nonneg (by exact_mod_cast Nat.zero_le N) (le_of_lt hδ)

  have hCB : 0 ≤ CB := by
    unfold CB
    apply Finset.sum_nonneg
    intro q hq
    apply mul_nonneg
    · exact norm_nonneg _
    · apply mul_nonneg
      · positivity
      · exact Real.exp_nonneg _

  have hF :
      ∀ s ∈ Kset,
        ‖arithmeticShiftedPrimeFStage n μ M s‖ ≤ CF := by
    unfold CF
    exact arithmeticShiftedPrimeFStage_bound_on_K_of_denominator_lower
      n μ M Kset δ hδ hgap

  have hB :
      ∀ s ∈ Kset,
        ‖arithmeticShiftedLaplaceBStage α s‖ ≤ CB := by
    unfold CB
    exact arithmeticShiftedLaplaceBStage_bound_on_K_of_region
      α Kset sigma hsigma hcenter hregion

  exact ArithmeticShiftedPrimeDExport_of_generic_F_B_bounds
    n μ M
    (arithmeticShiftedLaplaceBStage α)
    Kset
    CF
    CB
    hCF
    hCB
    hF
    hB

#print axioms ArithmeticShiftedPrimeDExport_of_spectral_gap_shiftedLaplaceBStage

end

end RHFormalization
