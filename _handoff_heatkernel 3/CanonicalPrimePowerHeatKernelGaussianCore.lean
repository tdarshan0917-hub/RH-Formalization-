import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummability

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelGaussianCore

Constant-stripping reduction for the heat-kernel weighted prime-power envelope.

This reduces the current target

  Summable (heatKernelExplicitWeightedEnvelope t)

to the true Gaussian core

  Summable (fun q => ‖q.weightC‖ * exp (-(q.center^2)/(4t))).
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The Gaussian core of the heat-kernel weighted envelope, with the factor
`(4πt)^(-1/2)` removed.
-/
noncomputable def heatKernelGaussianCoreEnvelope
    (t : ℝ) :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    ‖q.weightC‖ *
      Real.exp (-(q.center ^ 2) / (4 * t))

/--
The explicit heat-kernel envelope is exactly a constant multiple of the
Gaussian core.
-/
theorem heatKernelExplicitWeightedEnvelope_eq_const_mul_core
    (t : ℝ) :
    heatKernelExplicitWeightedEnvelope t =
      fun q : PrimePowerPair =>
        ((1 : ℝ) / Real.sqrt (4 * Real.pi * t)) *
          heatKernelGaussianCoreEnvelope t q := by
  funext q
  simp [heatKernelExplicitWeightedEnvelope, heatKernelGaussianCoreEnvelope]
  ring

/--
The explicit heat-kernel envelope is summable once the Gaussian core is summable.
-/
theorem heatKernelExplicitWeightedEnvelope_summable_of_core
    (t : ℝ)
    (h_core : Summable (heatKernelGaussianCoreEnvelope t)) :
    Summable (heatKernelExplicitWeightedEnvelope t) := by
  rw [heatKernelExplicitWeightedEnvelope_eq_const_mul_core t]
  exact h_core.mul_left ((1 : ℝ) / Real.sqrt (4 * Real.pi * t))

/--
The heat-kernel weighted envelope is summable once the Gaussian core is summable.
-/
theorem heatKernelWeightedEnvelope_summable_of_core
    (t : ℝ)
    (ht : 0 < t)
    (h_core : Summable (heatKernelGaussianCoreEnvelope t)) :
    Summable (heatKernelWeightedEnvelope t) := by
  exact
    heatKernelWeightedEnvelope_summable_of_explicit
      t
      ht
      (heatKernelExplicitWeightedEnvelope_summable_of_core t h_core)

end

end RHFormalization
