import RHFormalization.CanonicalPrimePowerHeatKernelLogGaussianTail
import RHFormalization.CanonicalPrimePowerHeatKernelPrimePowerSupport

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelGaussianMajorant

Bridge from the Nat log-Gaussian tail estimate to the PrimePowerPair
Gaussian-core envelope.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The log-Gaussian tail estimate applies to prime-power centers once `natValue`
is beyond a threshold.
-/
theorem exists_natValue_threshold_exp_neg_center_sq_le_inv_cube
    (t : ℝ)
    (ht : 0 < t) :
    ∃ N : ℕ,
      ∀ q : PrimePowerPair,
        N ≤ q.natValue →
          Real.exp (-(q.center ^ 2) / (4 * t)) ≤
            ((q.natValue : ℝ) ^ 3)⁻¹ := by
  rcases
    (eventually_atTop.1
      (eventually_exp_neg_log_sq_le_inv_cube t ht))
    with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro q hq
  have htail := hN q.natValue hq
  simpa [PrimePowerPair.center] using htail

/--
Beyond the same threshold, the Gaussian-core envelope is bounded by the
prime-power weight times `natValue^(-3)`.
-/
theorem heatKernelGaussianCoreEnvelope_le_weight_mul_natValue_inv_cube_of_ge
    (t : ℝ)
    (ht : 0 < t) :
    ∃ N : ℕ,
      ∀ q : PrimePowerPair,
        N ≤ q.natValue →
          heatKernelGaussianCoreEnvelope t q ≤
            ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹ := by
  rcases exists_natValue_threshold_exp_neg_center_sq_le_inv_cube t ht with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro q hq
  unfold heatKernelGaussianCoreEnvelope
  exact
    mul_le_mul_of_nonneg_left
      (hN q hq)
      (norm_nonneg q.weightC)

end

end RHFormalization
