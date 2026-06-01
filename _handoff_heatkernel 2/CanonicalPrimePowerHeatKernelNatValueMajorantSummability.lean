import RHFormalization.CanonicalPrimePowerHeatKernelGaussianMajorant

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

Arithmetic summability target for the natValue majorant.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The arithmetic majorant produced by the log-Gaussian tail estimate.
-/
noncomputable def heatKernelNatValueMajorant :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹

/--
Comparison principle for the natValue majorant.
-/
theorem heatKernelNatValueMajorant_summable_of_model
    (model : PrimePowerPair → ℝ)
    (h_model_summable : Summable model)
    (h_le_model :
      ∀ q : PrimePowerPair,
        heatKernelNatValueMajorant q ≤ model q) :
    Summable heatKernelNatValueMajorant := by
  refine
    Summable.of_nonneg_of_le
      ?h_nonneg
      h_le_model
      h_model_summable
  intro q
  unfold heatKernelNatValueMajorant
  exact
    mul_nonneg
      (norm_nonneg q.weightC)
      (by positivity)

/--
The current live theorem: the natValue majorant is summable.

This still contains `sorry`; the next real proof step is replacing this `sorry`.
-/
theorem heatKernelNatValueMajorant_summable :
    Summable heatKernelNatValueMajorant := by
  unfold heatKernelNatValueMajorant
  -- Current target:
  --   Summable
  --     (fun q : PrimePowerPair =>
  --       ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹)
  sorry

end

end RHFormalization
