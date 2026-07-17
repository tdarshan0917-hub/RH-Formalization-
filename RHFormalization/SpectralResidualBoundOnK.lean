import RHFormalization.ArithmeticPrimeSpectralGapDExport
import RHFormalization.ArithmeticPrimeShiftedLaplaceBStage
import RHFormalization.PrimePerturbedPayloadAligned
import RHFormalization.AppendixDKeyFormShortContract
import Mathlib

/-!
# Spectral residual bound: ‖R_stage‖ ≤ ‖F‖ + ‖B‖ on K, from the two banked s-side bounds.

R_stage = F - B, so ‖R_stage‖ ≤ ‖F‖ + ‖B‖. F bounded by N/δ (spectral gap),
B bounded by the spike-region sum. This is the per-stage residual bound on a compact,
the input to the D.ADM short-residual contract.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

/-- Per-stage residual bound on K from the F-gap bound + B-region bound. -/
theorem arithmeticPrime_residual_bound_on_K
    {N : ℕ} (n : ℕ) (μ : Fin N → ℝ) (K : Set ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ s ∈ K, ∀ i : Fin N,
      δ ≤ ‖s + ((perturbedEigenvalues μ
        (primePotential_isHermitian (primeStageWeights (N := N) n)) i : ℝ) : ℂ)‖)
    (α : DFiniteStage) (sigma : ℝ) (hsigma : 0 < sigma)
    (hcenter : ∀ q ∈ α.diagonalSpikeActiveIndices,
      0 ≤ PrimePowerPair.center (α.diagonalSpikeToPP q))
    (hregion : ∀ s ∈ K, sigma ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ∀ s ∈ K,
      ‖arithmeticPrimeFStage n μ s - arithmeticShiftedLaplaceBStage α s‖
        ≤ (N : ℝ) / δ
          + α.diagonalSpikeActiveIndices.sum
              (fun q => ‖α.diagonalSpikeContribution q‖ *
                ((1 / (2 * sigma)) *
                  Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma))) := by
  intro s hs
  have hF := arithmeticPrimeFStage_bound_on_K_of_denominator_lower n μ K δ hδ hgap s hs
  have hB := arithmeticShiftedLaplaceBStage_bound_on_K_of_region
    α K sigma hsigma hcenter hregion s hs
  calc
    ‖arithmeticPrimeFStage n μ s - arithmeticShiftedLaplaceBStage α s‖
        ≤ ‖arithmeticPrimeFStage n μ s‖ + ‖arithmeticShiftedLaplaceBStage α s‖ :=
          norm_sub_le _ _
    _ ≤ _ := add_le_add hF hB

#print axioms arithmeticPrime_residual_bound_on_K

end RHFormalization
