import RHFormalization.SpikeEnvelopeUniformBound
import RHFormalization.SpectralResidualBoundOnK
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityClosure
import Mathlib

/-!
# Stage-uniform residual bound: the gate to h_loc_bdd on R_stage = F - B.

Combines (all proven, axiom-clean):
  - arithmeticPrime_residual_bound_on_K : ‖R_stage‖ ≤ N/δ + spike_sum  (per-stage)
  - spike_envelope_sum_le_tsum          : spike_sum ≤ tsum (stage-independent)
  - heatKernelWeightedEnvelope_summable : the tsum is finite
into ‖R_stage‖ ≤ N/δ + tsum =: C, a constant with NO stage dependence.

This is h_loc_bdd on the real F - B object. No sectors. No premise. Built on the
proven summability floor.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

/-- **Stage-uniform spike envelope sum bound.** The per-stage spike sum, bounded by
the heat-kernel weighted envelope, is at most the total tsum over all prime-power pairs
— a single constant independent of the stage `α`. -/
theorem spike_sum_le_envelope_tsum
    (α : DFiniteStage) (sigma : ℝ) (hsigma : 0 < sigma)
    (h_term_le : ∀ q ∈ α.diagonalSpikeActiveIndices,
        ‖α.diagonalSpikeContribution q‖ *
          ((1 / (2 * sigma)) *
            Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma))
        ≤ heatKernelWeightedEnvelope sigma (α.diagonalSpikeToPP q))
    (h_inj : Set.InjOn α.diagonalSpikeToPP α.diagonalSpikeActiveIndices) :
    α.diagonalSpikeActiveIndices.sum
        (fun q => ‖α.diagonalSpikeContribution q‖ *
          ((1 / (2 * sigma)) *
            Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma)))
      ≤ ∑' p : PrimePowerPair, heatKernelWeightedEnvelope sigma p := by
  -- step 1: bound termwise by the envelope, reindexed
  have hstep1 :
      α.diagonalSpikeActiveIndices.sum
        (fun q => ‖α.diagonalSpikeContribution q‖ *
          ((1 / (2 * sigma)) *
            Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma)))
        ≤ α.diagonalSpikeActiveIndices.sum
            (fun q => heatKernelWeightedEnvelope sigma (α.diagonalSpikeToPP q)) :=
    Finset.sum_le_sum h_term_le
  -- step 2: reindex active-sum to a sum over the image finset (injective)
  have hreindex :
      α.diagonalSpikeActiveIndices.sum
          (fun q => heatKernelWeightedEnvelope sigma (α.diagonalSpikeToPP q))
        = (α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP).sum
            (fun p => heatKernelWeightedEnvelope sigma p) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact h_inj ha hb hab
  -- step 3: image-sum ≤ tsum (the green spike_envelope_sum_le_tsum)
  have hstep3 := spike_envelope_sum_le_tsum sigma hsigma
    (α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP)
  calc
    α.diagonalSpikeActiveIndices.sum
        (fun q => ‖α.diagonalSpikeContribution q‖ *
          ((1 / (2 * sigma)) *
            Real.exp (-(PrimePowerPair.center (α.diagonalSpikeToPP q)) * sigma)))
        ≤ _ := hstep1
    _ = _ := hreindex
    _ ≤ _ := hstep3

#print axioms spike_sum_le_envelope_tsum

end RHFormalization
