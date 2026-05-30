import RHFormalization.DOperatorExport
import RHFormalization.PrimePowerWeightNormalizationLock

/-!
# RHFormalization.DPrimePowerNormalizationConcrete

Concrete theorem-backed D-side prime-power normalization.

This file removes the old `True`-shaped normalization placeholder by making the
D-side normalization exactly

  weight q = spikeWeight (lambdaWeight q) q = lambdaWeight q / sqrt q.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build a D-side prime-power normalization from a center map and a numerator map.
The weight is definitionally the frozen manuscript normalization.
-/
def buildDPrimePowerNormalizationFromLambda
    (center lambdaWeight : ℝ → ℝ) :
    DPrimePowerNormalization :=
  { center := center
    lambdaWeight := lambdaWeight
    weight := fun q : ℝ => spikeWeight (lambdaWeight q) q
    h_weight_eq_spikeWeight := by
      intro q
      rfl }

/--
Every theorem-backed `DPrimePowerNormalization` uses the square-root denominator.
-/
theorem DPrimePowerNormalization.weight_eq_lambda_div_sqrt
    (N : DPrimePowerNormalization)
    (q : ℝ) :
    N.weight q = N.lambdaWeight q / Real.sqrt q := by
  rw [N.h_weight_eq_spikeWeight q]
  rfl

/--
Concrete constructor also expands directly to the square-root denominator.
-/
theorem buildDPrimePowerNormalizationFromLambda_weight_eq
    (center lambdaWeight : ℝ → ℝ)
    (q : ℝ) :
    (buildDPrimePowerNormalizationFromLambda center lambdaWeight).weight q =
      lambdaWeight q / Real.sqrt q := by
  rfl

end

end RHFormalization
