import RHFormalization.CanonicalPrimePowerHeatKernelPrimePowerSupport
import RHFormalization.CanonicalPrimePowerHeatKernelLogGaussianTail

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

theorem heatKernelGaussianCoreEnvelope_summable
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelGaussianCoreEnvelope t) := by
  rw [heatKernelGaussianCoreEnvelope_eq_abs_weightReal]
  show
    Summable
      (fun q : PrimePowerPair =>
        |q.weightReal| *
          Real.exp (-(q.center ^ 2) / (4 * t)))
  -- next proof step: compare to the natValue^-3 majorant using
  -- eventually_exp_neg_log_sq_le_inv_cube
  sorry

end

end RHFormalization
