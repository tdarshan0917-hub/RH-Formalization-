import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCore

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreBounds

First proof lemmas for the Gaussian-core summability theorem.

This file removes the complex norm from the active target and proves
nonnegativity of the Gaussian-core summand.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The complex norm of the prime-power weight is the absolute value of the real
weight.
-/
theorem norm_weightC_eq_abs_weightReal
    (q : PrimePowerPair) :
    ‖q.weightC‖ = |q.weightReal| := by
  simpa [PrimePowerPair.weightC] using Complex.norm_ofReal q.weightReal

/--
Expanded real form of the Gaussian-core envelope.
-/
theorem heatKernelGaussianCoreEnvelope_eq_abs_weightReal
    (t : ℝ) :
    heatKernelGaussianCoreEnvelope t =
      fun q : PrimePowerPair =>
        |q.weightReal| *
          Real.exp (-(q.center ^ 2) / (4 * t)) := by
  funext q
  simp [heatKernelGaussianCoreEnvelope, norm_weightC_eq_abs_weightReal]

/--
The Gaussian-core summand is nonnegative.
-/
theorem heatKernelGaussianCoreEnvelope_nonneg
    (t : ℝ)
    (q : PrimePowerPair) :
    0 ≤ heatKernelGaussianCoreEnvelope t q := by
  unfold heatKernelGaussianCoreEnvelope
  exact
    mul_nonneg
      (norm_nonneg q.weightC)
      (le_of_lt (Real.exp_pos _))

end

end RHFormalization
