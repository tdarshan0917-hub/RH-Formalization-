import RHFormalization.ArithmeticShiftedEigenvalueNonneg
import RHFormalization.BallCutDistance

/-!
# ArithmeticShiftedPrimeDExportOnBall

Corrected closed-ball finite-stage D.EXPORT.

This file removes the abstract spectral-gap hypothesis by combining:

* Weyl/growthDrop shift condition ⇒ shifted perturbed eigenvalues nonnegative;
* closedBall c r ⊆ Ω ⇒ uniform denominator gap;
* shifted arithmetic prime F-stage;
* live shifted-Laplace B-stage.

Remaining local hypotheses:
* active centers are nonnegative;
* shifted-Laplace sqrt-region lower bound.
-/

namespace RHFormalization

noncomputable section

open Complex Metric
open scoped BigOperators Classical

/--
On a closed ball contained in Ω, the Weyl/growthDrop shift condition gives
a uniform denominator gap for the corrected shifted arithmetic F-stage.
-/
theorem arithmeticShiftedPrime_denominator_gap_on_closedBall_of_free_growthDrop_le
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Ω)
    (hfree :
      ∀ i : Fin N,
        growthDrop (primePotential (primeStageWeights (N := N) n))
          ≤ freeEigenvalues (μShift μ M) i) :
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
    arithmeticShiftedPerturbedEigenvalues_nonneg_of_free_growthDrop_le
      n μ M hfree

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
Corrected finite-stage D.EXPORT on a closed Ω-ball.

No dead displacement kernel.
No unshifted F-stage.
No abstract spectral-gap hypothesis.
No separate `hpos` hypothesis.

The only remaining local assumptions are:
* the global shift is large enough in the Weyl/growthDrop sense;
* active centers are nonnegative;
* the shifted-Laplace region lower bound holds on the ball.
-/
theorem ArithmeticShiftedPrimeDExport_on_closedBall_shiftedLaplaceBStage
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Ω)
    (hfree :
      ∀ i : Fin N,
        growthDrop (primePotential (primeStageWeights (N := N) n))
          ≤ freeEigenvalues (μShift μ M) i)
    (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hcenter :
      ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center
          ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q))
    (hregion :
      ∀ s ∈ Metric.closedBall c r,
        sigma ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    PerturbedDExport
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      (Metric.closedBall c r) := by
  obtain ⟨δ, hδ, hgap⟩ :=
    arithmeticShiftedPrime_denominator_gap_on_closedBall_of_free_growthDrop_le
      n μ M c r hr hball hfree

  exact ArithmeticShiftedPrimeDExport_of_spectral_gap_shiftedLaplaceBStage
    n μ M hnn
    (Metric.closedBall c r)
    δ
    sigma
    hδ
    hgap
    hsigma
    hcenter
    hregion

#print axioms arithmeticShiftedPrime_denominator_gap_on_closedBall_of_free_growthDrop_le
#print axioms ArithmeticShiftedPrimeDExport_on_closedBall_shiftedLaplaceBStage

end

end RHFormalization
