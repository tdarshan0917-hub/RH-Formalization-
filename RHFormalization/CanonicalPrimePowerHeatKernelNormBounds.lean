import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelNormBounds

Pointwise norm bounds for the concrete heat-kernel weighted summability target.

The key correction is that `heatKernelG` is now explicitly a real Gaussian
coerced to `ℂ`, so its norm is the absolute value of a nonnegative real scalar.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The real scalar expression underlying the heat kernel.
-/
noncomputable def heatKernelRealScalar (t : ℝ) (a : ℝ) : ℝ :=
  (1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
    Real.exp (-(a ^ 2) / (4 * t))

/--
`heatKernelG` is the real scalar Gaussian coerced to `ℂ`.
-/
theorem heatKernelG_eq_realScalar
    (t a : ℝ) :
    heatKernelG t a = Complex.ofReal (heatKernelRealScalar t a) := by
  rfl

/--
For positive heat time, the real scalar heat kernel is nonnegative.
-/
theorem heatKernelRealScalar_nonneg
    (t a : ℝ)
    (ht : 0 < t) :
    0 ≤ heatKernelRealScalar t a := by
  unfold heatKernelRealScalar
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmul : 0 < 4 * Real.pi * t := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) := by
    exact Real.sqrt_pos.2 hmul
  have hcoef_nonneg :
      0 ≤ (1 : ℝ) / Real.sqrt (4 * Real.pi * t) := by
    exact div_nonneg zero_le_one (le_of_lt hsqrt_pos)
  have hexp_nonneg :
      0 ≤ Real.exp (-(a ^ 2) / (4 * t)) := by
    exact le_of_lt (Real.exp_pos _)
  exact mul_nonneg hcoef_nonneg hexp_nonneg

/--
Norm of the complex-valued heat kernel is exactly the real scalar heat kernel
for positive heat time.
-/
theorem norm_heatKernelG_eq_realScalar
    (t a : ℝ)
    (ht : 0 < t) :
    ‖heatKernelG t a‖ = heatKernelRealScalar t a := by
  rw [heatKernelG_eq_realScalar]
  have hnonneg : 0 ≤ heatKernelRealScalar t a :=
    heatKernelRealScalar_nonneg t a ht
  simpa [abs_of_nonneg hnonneg]

/--
Expanded norm identity for `heatKernelG`.
-/
theorem norm_heatKernelG_eq
    (t a : ℝ)
    (ht : 0 < t) :
    ‖heatKernelG t a‖ =
      (1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
        Real.exp (-(a ^ 2) / (4 * t)) := by
  simpa [heatKernelRealScalar] using
    norm_heatKernelG_eq_realScalar t a ht

/--
Expanded form of the heat-kernel weighted envelope.
-/
theorem heatKernelWeightedEnvelope_apply_expanded
    (t : ℝ)
    (ht : 0 < t)
    (q : PrimePowerPair) :
    heatKernelWeightedEnvelope t q =
      ‖q.weightC‖ *
        ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
          Real.exp (-(q.center ^ 2) / (4 * t))) := by
  rw [heatKernelWeightedEnvelope_apply]
  rw [norm_heatKernelG_eq t q.center ht]

end

end RHFormalization
