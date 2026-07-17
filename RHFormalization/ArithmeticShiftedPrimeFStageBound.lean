import RHFormalization.PrimeShiftedFStageConsistency
import RHFormalization.ArithmeticPrimeShiftedLaplaceBStage
import RHFormalization.BallCutDistance

/-!
# ArithmeticShiftedPrimeFStageBound

This file switches the final DExport route to the shifted F-stage, aligned with
the nonnegative native operator:

  arithmeticShiftedPrimeFStage n μ M

rather than the unshifted arithmeticPrimeFStage.
-/

namespace RHFormalization

noncomputable section

open Complex Metric
open scoped BigOperators Classical

/--
Shifted arithmetic prime F-stage bound from a direct denominator lower bound.
-/
theorem arithmeticShiftedPrimeFStage_bound_on_K_of_denominator_lower
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (K : Set ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hgap :
      ∀ s ∈ K,
        ∀ i : Fin N,
          δ ≤ ‖s +
            ((perturbedEigenvalues
              (μShift μ M)
              (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖) :
    ∀ s ∈ K,
      ‖arithmeticShiftedPrimeFStage n μ M s‖ ≤
        (N : ℝ) / δ := by
  intro s hs
  unfold arithmeticShiftedPrimeFStage primeShiftedPerturbedFStage
  rw [primePerturbedFStage_eq]
  unfold FstageFinite
  calc
    ‖∑ i : Fin N,
        (s +
          ((perturbedEigenvalues
            (μShift μ M)
            (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ))⁻¹‖
        ≤ ∑ i : Fin N,
            ‖(s +
              ((perturbedEigenvalues
                (μShift μ M)
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
Generic DExport for the shifted arithmetic F-stage.

This is the safe bridge: shifted F-bound + arbitrary B-bound.
-/
theorem ArithmeticShiftedPrimeDExport_of_generic_F_B_bounds
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (B : ℂ → ℂ)
    (K : Set ℂ)
    (CF CB : ℝ)
    (hCF : 0 ≤ CF)
    (hCB : 0 ≤ CB)
    (hF : ∀ s ∈ K, ‖arithmeticShiftedPrimeFStage n μ M s‖ ≤ CF)
    (hB : ∀ s ∈ K, ‖B s‖ ≤ CB) :
    PerturbedDExport
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      B K := by
  unfold PerturbedDExport
  refine ⟨CF + CB, add_nonneg hCF hCB, ?_⟩
  intro s hs
  unfold perturbedResidual
  calc
    ‖perturbedFStage
        (μShift μ M)
        (primePotential_isHermitian (primeStageWeights (N := N) n)) s - B s‖
        ≤ ‖perturbedFStage
              (μShift μ M)
              (primePotential_isHermitian (primeStageWeights (N := N) n)) s‖
          + ‖B s‖ := by
            simpa [sub_eq_add_neg, norm_neg] using
              norm_add_le
                (perturbedFStage
                  (μShift μ M)
                  (primePotential_isHermitian (primeStageWeights (N := N) n)) s)
                (-(B s))
    _ ≤ CF + CB := by
          exact add_le_add
            (by
              simpa [arithmeticShiftedPrimeFStage, primeShiftedPerturbedFStage, primePerturbedFStage]
                using hF s hs)
            (hB s hs)

#print axioms arithmeticShiftedPrimeFStage_bound_on_K_of_denominator_lower
#print axioms ArithmeticShiftedPrimeDExport_of_generic_F_B_bounds

end

end RHFormalization
