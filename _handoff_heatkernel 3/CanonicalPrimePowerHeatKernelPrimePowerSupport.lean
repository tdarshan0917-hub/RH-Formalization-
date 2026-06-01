import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreBounds

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelPrimePowerSupport

Support and valid-prime-power expansion lemmas for the Gaussian-core summability
theorem.

These are direct proof lemmas for:

  Summable (heatKernelGaussianCoreEnvelope t)

They show:
* invalid prime-power pairs contribute zero;
* valid prime-power pairs have the exact expected summand.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Non-prime-power indices contribute zero to the Gaussian-core envelope.
-/
theorem heatKernelGaussianCoreEnvelope_eq_zero_of_not_isPrimePowerPair
    (t : ℝ)
    (q : PrimePowerPair)
    (hq : ¬ IsPrimePowerPair q) :
    heatKernelGaussianCoreEnvelope t q = 0 := by
  unfold heatKernelGaussianCoreEnvelope
  simp [PrimePowerPair.weightC, PrimePowerPair.weightReal, hq]

/--
On valid prime-power pairs, the Gaussian-core envelope is exactly the real
weight formula times the Gaussian decay.
-/
theorem heatKernelGaussianCoreEnvelope_eq_valid_primePower_formula
    (t : ℝ)
    (q : PrimePowerPair)
    (hq : IsPrimePowerPair q) :
    heatKernelGaussianCoreEnvelope t q =
      |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| *
        Real.exp (-(q.center ^ 2) / (4 * t)) := by
  rw [heatKernelGaussianCoreEnvelope_eq_abs_weightReal]
  simp [PrimePowerPair.weightReal, hq]

end

end RHFormalization
