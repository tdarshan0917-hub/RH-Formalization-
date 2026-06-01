import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreBounds

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

example
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelGaussianCoreEnvelope t) := by
  rw [heatKernelGaussianCoreEnvelope_eq_abs_weightReal]
  show
    Summable
      (fun q : PrimePowerPair =>
        |q.weightReal| *
          Real.exp (-(q.center ^ 2) / (4 * t)))
  -- This is the real theorem.
  -- Next proof step is comparison to a summable majorant.
