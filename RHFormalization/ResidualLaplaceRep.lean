import RHFormalization.BStageLaplaceLift
import RHFormalization.DA2HeatTrace
import RHFormalization.ArithmeticPrimeOperatorResidual
import Mathlib

/-!
# R = F − B = ∫ e^{-st} Q_res  (manuscript p164 line 13)

The Stieltjes pole-package identity (manuscript title): frequency-side F−B equals
the Laplace transform of the time-side residual Q_res(t) = Tr(e^{-tH}) − heat spikes.
Green modulo the single named B-connector.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The time-residual integrand Q_res(t) = (heat trace integrand) − (heat spikes integrand). -/
noncomputable def qResIntegrand
    (n : ℕ) (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) (t : ℝ) : ℂ :=
  (∑ i, Complex.exp (-(s +
        ((perturbedEigenvalues μ (primePotential_isHermitian
          (primeStageWeights (N := N) n)) i : ℝ) : ℂ)) * (t:ℂ)))
  - bStageHeatIntegrand α s t

/-- **R = F − B = ∫ e^{-st} Q_res** (p164 line 13). Green modulo the single named B-connector. -/
theorem arithmeticPrimeResidual_eq_laplace_qRes
    (n : ℕ) (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) (hs : 0 < s.re)
    (hlam : ∀ i, 0 ≤ perturbedEigenvalues μ (primePotential_isHermitian
              (primeStageWeights (N := N) n)) i)
    (hcenter : ∀ q ∈ α.diagonalSpikeActiveIndices,
      0 ≤ PrimePowerPair.center (α.diagonalSpikeToPP q))
    (hintF : MeasureTheory.IntegrableOn
        (fun t : ℝ => ∑ i, Complex.exp (-(s +
          ((perturbedEigenvalues μ (primePotential_isHermitian
            (primeStageWeights (N := N) n)) i : ℝ) : ℂ)) * (t:ℂ))) (Set.Ioi (0:ℝ)))
    (hintB : MeasureTheory.IntegrableOn
        (fun t : ℝ => bStageHeatIntegrand α s t) (Set.Ioi (0:ℝ)))
    (hintSpike : ∀ q ∈ α.diagonalSpikeActiveIndices,
      MeasureTheory.IntegrableOn
        (fun t : ℝ => shiftedHeatIntegrand (PrimePowerPair.center (α.diagonalSpikeToPP q)) s t)
        (Set.Ioi (0:ℝ))) :
    arithmeticPrimeFStage n μ s - arithmeticShiftedLaplaceBStage α s
      = ∫ t in Set.Ioi (0:ℝ), qResIntegrand n μ α s t := by
  unfold qResIntegrand
  rw [MeasureTheory.integral_sub hintF hintB]
  congr 1
  · -- F side
    rw [arithmeticPrimeFStage, primePerturbedFStage_eq]
    exact FstageFinite_eq_laplace_heatTrace _ hlam s hs
  · -- B side
    exact arithmeticShiftedLaplaceBStage_eq_laplace α s hs hcenter hintSpike

#print axioms arithmeticPrimeResidual_eq_laplace_qRes

end RHFormalization
