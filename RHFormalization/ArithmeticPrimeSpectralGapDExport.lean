import RHFormalization.ArithmeticPrimeShiftedLaplaceBStage

/-!
# ArithmeticPrimeSpectralGapDExport

This file replaces the temporary `|Im s|` F-bound by the correct denominator
gap bound:

  δ ≤ ‖s + λ_i‖

for every arithmetic prime eigenvalue λ_i.

This is the right fixed-stage theorem for Ω-compact work.  The next step after
this file is to prove such a δ exists for compact K ⊂ Ω when the spectrum is
nonnegative.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
Arithmetic prime F-stage bound from a direct denominator lower bound.

This is better than the temporary `|Im s|` bound because it can apply on real
positive points of Ω as well, not only off the real axis.
-/
theorem arithmeticPrimeFStage_bound_on_K_of_denominator_lower
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (K : Set ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hgap :
      ∀ s ∈ K,
        ∀ i : Fin N,
          δ ≤ ‖s +
            ((perturbedEigenvalues μ
              (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖) :
    ∀ s ∈ K,
      ‖arithmeticPrimeFStage n μ s‖ ≤
        (N : ℝ) / δ := by
  intro s hs
  unfold arithmeticPrimeFStage
  rw [primePerturbedFStage_eq]
  unfold FstageFinite
  calc
    ‖∑ i : Fin N,
        (s +
          ((perturbedEigenvalues μ
            (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ))⁻¹‖
        ≤ ∑ i : Fin N,
            ‖(s +
              ((perturbedEigenvalues μ
                (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ))⁻¹‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (1 / δ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_inv, inv_eq_one_div]
          exact one_div_le_one_div_of_le hδ (hgap s hs i)
    _ = (N : ℝ) / δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/--
Corrected fixed-stage D.EXPORT using:

* arithmetic prime F-stage;
* live shifted-Laplace B-stage;
* direct spectral denominator gap;
* shifted-Laplace kernel region bound.

No displacement kernel and no `|Im s|` hypothesis.
-/
theorem ArithmeticPrimeDExport_of_spectral_gap_shiftedLaplaceBStage
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
            ((perturbedEigenvalues μ
              (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖)
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
        ‖arithmeticPrimeFStage n μ s‖ ≤ CF := by
    unfold CF
    exact arithmeticPrimeFStage_bound_on_K_of_denominator_lower
      n μ Kset δ hδ hgap

  have hB :
      ∀ s ∈ Kset,
        ‖arithmeticShiftedLaplaceBStage α s‖ ≤ CB := by
    unfold CB
    exact arithmeticShiftedLaplaceBStage_bound_on_K_of_region
      α Kset sigma hsigma hcenter hregion

  exact ArithmeticPrimeDExport_of_generic_F_B_bounds
    n μ
    (arithmeticShiftedLaplaceBStage α)
    Kset
    CF
    CB
    hCF
    hCB
    hF
    hB

#print axioms arithmeticPrimeFStage_bound_on_K_of_denominator_lower
#print axioms ArithmeticPrimeDExport_of_spectral_gap_shiftedLaplaceBStage

end

end RHFormalization
