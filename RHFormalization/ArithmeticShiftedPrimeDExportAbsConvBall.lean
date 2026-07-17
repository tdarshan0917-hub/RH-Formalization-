import RHFormalization.ArithmeticShiftedPrimeDExportOnBall

/-!
# ArithmeticShiftedPrimeDExportAbsConvBall

This file removes the explicit shifted-Laplace region hypothesis by assuming the
closed ball lies inside `shiftedLaplaceAbsConvRegion`.

Since
  shiftedLaplaceAbsConvRegion = {s | 1/2 < Re sqrt(s + 1/4)},
we may take sigma = 1/2.

This leaves only:
* the Weyl/growthDrop large-shift condition;
* active prime-power centers are nonnegative.
-/

namespace RHFormalization

noncomputable section

open Complex Metric
open scoped BigOperators Classical

/--
If a closed ball is contained in the shifted-Laplace absolute convergence
region, then `Re sqrt(s+1/4) ≥ 1/2` on the ball.
-/
theorem shiftedLaplace_region_half_on_closedBall
    (c : ℂ)
    (r : ℝ)
    (hVball : Metric.closedBall c r ⊆ shiftedLaplaceAbsConvRegion) :
    ∀ s ∈ Metric.closedBall c r,
      ((1 : ℝ) / 2) ≤ (Complex.sqrt (s + (1/4 : ℂ))).re := by
  intro s hs
  exact le_of_lt (hVball hs)

/--
Corrected finite-stage D.EXPORT on a closed ball contained in the shifted-Laplace
absolute convergence region.

No dead displacement kernel.
No unshifted F-stage.
No abstract spectral-gap hypothesis.
No separate `hpos`.
No separate `hregion`.

Remaining local assumptions:
* the global shift is large enough in the Weyl/growthDrop/free-spectrum sense;
* active prime-power centers are nonnegative.
-/
theorem ArithmeticShiftedPrimeDExport_on_absConv_closedBall_shiftedLaplaceBStage
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
    (hVball : Metric.closedBall c r ⊆ shiftedLaplaceAbsConvRegion)
    (hfree :
      ∀ i : Fin N,
        growthDrop (primePotential (primeStageWeights (N := N) n))
          ≤ freeEigenvalues (μShift μ M) i)
    (hcenter :
      ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
        0 ≤ PrimePowerPair.center
          ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q)) :
    PerturbedDExport
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      (Metric.closedBall c r) := by
  have hball : Metric.closedBall c r ⊆ Ω := by
    intro s hs
    exact shiftedLaplaceAbsConvRegion_subset_Omega (hVball hs)

  have hsigma : 0 < ((1 : ℝ) / 2) := by
    norm_num

  have hregion :
      ∀ s ∈ Metric.closedBall c r,
        ((1 : ℝ) / 2) ≤ (Complex.sqrt (s + (1/4 : ℂ))).re :=
    shiftedLaplace_region_half_on_closedBall c r hVball

  exact ArithmeticShiftedPrimeDExport_on_closedBall_shiftedLaplaceBStage
    n μ M hnn
    c r hr
    hball
    hfree
    ((1 : ℝ) / 2)
    hsigma
    hcenter
    hregion

#print axioms shiftedLaplace_region_half_on_closedBall
#print axioms ArithmeticShiftedPrimeDExport_on_absConv_closedBall_shiftedLaplaceBStage

end

end RHFormalization
