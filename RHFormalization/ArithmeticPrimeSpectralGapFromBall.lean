import RHFormalization.ArithmeticPrimeSpectralGapDExport
import RHFormalization.BallCutDistance

/-!
# ArithmeticPrimeSpectralGapFromBall

This file removes the abstract spectral-gap hypothesis from the corrected
shifted-Laplace D.EXPORT theorem on closed balls contained in Ω.

It uses the existing `BallCutDistance.exists_uniform_lower_bound_on_ball`.

This is the right Ω-compatible replacement for the earlier `|Im s|` condition.
-/

namespace RHFormalization

noncomputable section

open Complex Metric
open scoped BigOperators Classical

/--
On a closed ball contained in Ω, nonnegative arithmetic-prime eigenvalues give
a uniform denominator gap for the finite arithmetic F-stage.
-/
theorem arithmeticPrime_denominator_gap_on_closedBall
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Ω)
    (hpos :
      ∀ i : Fin N,
        0 ≤ perturbedEigenvalues μ
          (primePotential_isHermitian (primeStageWeights (N := N) n)) i) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ s ∈ Metric.closedBall c r,
        ∀ i : Fin N,
          δ ≤ ‖s +
            ((perturbedEigenvalues μ
              (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖ := by
  obtain ⟨δ, hδ, hδbound⟩ :=
    exists_uniform_lower_bound_on_ball c r hr hball
  refine ⟨δ, hδ, ?_⟩
  intro s hs i
  exact hδbound s hs
    (perturbedEigenvalues μ
      (primePotential_isHermitian (primeStageWeights (N := N) n)) i)
    (hpos i)

/--
Corrected fixed-stage D.EXPORT on an Ω-ball.

Inputs left:
* nonnegative arithmetic-prime perturbed spectrum;
* shifted-Laplace region lower bound;
* active prime-power centers are nonnegative.

No displacement kernel. No `|Im s|` hypothesis. No abstract spectral-gap
hypothesis.
-/
theorem ArithmeticPrimeDExport_on_closedBall_shiftedLaplaceBStage
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
    (hpos :
      ∀ i : Fin N,
        0 ≤ perturbedEigenvalues μ
          (primePotential_isHermitian (primeStageWeights (N := N) n)) i)
    (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hcenter :
      ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center
          ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q))
    (hregion :
      ∀ s ∈ Metric.closedBall c r,
        sigma ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ArithmeticPrimeDExport n μ
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      (Metric.closedBall c r) := by
  obtain ⟨δ, hδ, hgap⟩ :=
    arithmeticPrime_denominator_gap_on_closedBall
      n μ c r hr hball hpos
  exact ArithmeticPrimeDExport_of_spectral_gap_shiftedLaplaceBStage
    n μ M hnn
    (Metric.closedBall c r)
    δ
    sigma
    hδ
    hgap
    hsigma
    hcenter
    hregion

#print axioms arithmeticPrime_denominator_gap_on_closedBall
#print axioms ArithmeticPrimeDExport_on_closedBall_shiftedLaplaceBStage

end

end RHFormalization
