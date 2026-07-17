import RHFormalization.ArithmeticShiftedEigenvalueNonnegFromPositive

/-!
# ArithmeticShiftedPrimeDExportFromHnn

Local finite-stage close.

This removes the final local finite-stage assumption `hfree` by using:

  hnn ⇒ shifted perturbed eigenvalues are nonnegative.

Then the Ω-ball denominator lemma gives the spectral gap, and the already-corrected
shifted-Laplace DExport theorem applies.

Result:

  closedBall c r ⊆ shiftedLaplaceAbsConvRegion
  + native shifted quadratic-form nonnegativity hnn
  ⇒ corrected shifted-Laplace PerturbedDExport.

No dead displacement kernel.
No unshifted F-stage.
No abstract hgap.
No separate hpos.
No hregion.
No hcenter.
No hfree.
-/

namespace RHFormalization

noncomputable section

open Complex Metric
open scoped BigOperators Classical

/--
On a closed ball contained in Ω, native shifted nonnegativity gives a uniform
denominator gap for the corrected shifted arithmetic F-stage.
-/
theorem arithmeticShiftedPrime_denominator_gap_on_closedBall_of_hnn
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights (N := N) n) M y)))
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Ω) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ s ∈ Metric.closedBall c r,
        ∀ i : Fin N,
          δ ≤ ‖s +
            ((perturbedEigenvalues
              (μShift μ M)
              (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖ := by
  have hpos :
      ∀ i : Fin N,
        0 ≤ perturbedEigenvalues
          (μShift μ M)
          (primePotential_isHermitian (primeStageWeights (N := N) n)) i :=
    arithmeticShiftedPerturbedEigenvalues_nonneg_of_hnn n μ M hnn

  obtain ⟨δ, hδ, hδbound⟩ :=
    exists_uniform_lower_bound_on_ball c r hr hball

  refine ⟨δ, hδ, ?_⟩
  intro s hs i
  exact hδbound s hs
    (perturbedEigenvalues
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n)) i)
    (hpos i)

/--
Corrected local finite-stage DExport from native shifted nonnegativity.

This is the local finite-stage target:
`hfree` has been removed.
-/
theorem ArithmeticShiftedPrimeDExport_on_absConv_closedBall_from_hnn
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights (N := N) n) M y)))
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hVball : Metric.closedBall c r ⊆ shiftedLaplaceAbsConvRegion) :
    PerturbedDExport
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      (Metric.closedBall c r) := by
  have hball : Metric.closedBall c r ⊆ Ω := by
    intro s hs
    exact shiftedLaplaceAbsConvRegion_subset_Omega (hVball hs)

  obtain ⟨δ, hδ, hgap⟩ :=
    arithmeticShiftedPrime_denominator_gap_on_closedBall_of_hnn
      n μ M hnn c r hr hball

  have hsigma : 0 < ((1 : ℝ) / 2) := by
    norm_num

  have hregion :
      ∀ s ∈ Metric.closedBall c r,
        ((1 : ℝ) / 2) ≤ (Complex.sqrt (s + (1/4 : ℂ))).re :=
    shiftedLaplace_region_half_on_closedBall c r hVball

  have hcenter :
      ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center
          ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q) :=
    arithmeticPrimeOperatorDFiniteStage_active_center_nonneg n μ M hnn

  exact ArithmeticShiftedPrimeDExport_of_spectral_gap_shiftedLaplaceBStage
    n μ M hnn
    (Metric.closedBall c r)
    δ
    ((1 : ℝ) / 2)
    hδ
    hgap
    hsigma
    hcenter
    hregion

#print axioms arithmeticShiftedPrime_denominator_gap_on_closedBall_of_hnn
#print axioms ArithmeticShiftedPrimeDExport_on_absConv_closedBall_from_hnn

end

end RHFormalization
