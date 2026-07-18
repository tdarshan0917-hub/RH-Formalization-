import RHFormalization.ShiftedLaplaceRegularFromZeroDensity

/-!
# RHFormalization.ShiftedLaplaceBRegularAtomic

Atomic analytic step toward shifted/Laplace `hB_regular`.

This version avoids the previous sign-normal-form trap:
we never use `.neg` on `a * sqrt`; instead we keep the exponent argument as

  (-(a : ℂ)) * shiftedLaplaceSqrt s

which matches the printed kernel definition.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- The shifted square-root appearing in the shifted/Laplace kernel. -/
abbrev shiftedLaplaceSqrt (s : ℂ) : ℂ :=
  Complex.sqrt (s + (1 / 4 : ℂ))

#check shiftedLaplaceHeatKernelC
#check shiftedLaplacePrimePackageAt
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum

/--
Atomic holomorphy of the shifted/Laplace heat kernel term, assuming the shifted
square-root branch is holomorphic and nonzero at the point.
-/
theorem shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
    (a : ℝ)
    (z : ℂ)
    (h_sqrt :
      HolomorphicAtC shiftedLaplaceSqrt z)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (fun s : ℂ => shiftedLaplaceHeatKernelC a s)
      z := by
  have hden_ne :
      (2 : ℂ) * shiftedLaplaceSqrt z ≠ 0 := by
    exact mul_ne_zero (by norm_num) h_sqrt_ne

  have h_two :
      HolomorphicAtC (fun _ : ℂ => (2 : ℂ)) z := by
    exact analyticAt_const

  have h_den :
      HolomorphicAtC
        (fun s : ℂ => (2 : ℂ) * shiftedLaplaceSqrt s)
        z := by
    simpa [Pi.mul_apply] using h_two.mul h_sqrt

  have h_inv_den :
      HolomorphicAtC
        (fun s : ℂ => ((2 : ℂ) * shiftedLaplaceSqrt s)⁻¹)
        z := by
    exact h_den.inv hden_ne

  have h_frac :
      HolomorphicAtC
        (fun s : ℂ => (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s))
        z := by
    simpa [one_div, div_eq_mul_inv] using h_inv_den

  have h_neg_a :
      HolomorphicAtC (fun _ : ℂ => (-(a : ℂ))) z := by
    exact analyticAt_const

  have h_arg :
      HolomorphicAtC
        (fun s : ℂ => (-(a : ℂ)) * shiftedLaplaceSqrt s)
        z := by
    simpa [Pi.mul_apply] using h_neg_a.mul h_sqrt

  have h_exp :
      HolomorphicAtC
        (fun s : ℂ =>
          Complex.exp ((-(a : ℂ)) * shiftedLaplaceSqrt s))
        z := by
    exact h_arg.cexp

  have h_prod :
      HolomorphicAtC
        (fun s : ℂ =>
          (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s) *
            Complex.exp ((-(a : ℂ)) * shiftedLaplaceSqrt s))
        z := by
    simpa [Pi.mul_apply] using h_frac.mul h_exp

  simpa [shiftedLaplaceHeatKernelC, shiftedLaplaceSqrt] using h_prod

/--
The weighted prime-power term is holomorphic under the same shifted-sqrt
hypotheses.
-/
theorem shiftedLaplaceWeightedTerm_holomorphicAt_of_shiftedSqrt
    (q : PrimePowerPair)
    (z : ℂ)
    (h_sqrt :
      HolomorphicAtC shiftedLaplaceSqrt z)
    (h_sqrt_ne :
      shiftedLaplaceSqrt z ≠ 0) :
    HolomorphicAtC
      (fun s : ℂ =>
        q.weightC * shiftedLaplaceHeatKernelC q.center s)
      z := by
  have h_const :
      HolomorphicAtC (fun _ : ℂ => q.weightC) z := by
    exact analyticAt_const

  have h_kernel :
      HolomorphicAtC
        (fun s : ℂ => shiftedLaplaceHeatKernelC q.center s)
        z :=
    shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
      q.center z h_sqrt h_sqrt_ne

  simpa [Pi.mul_apply] using h_const.mul h_kernel

#print axioms shiftedLaplaceSqrt
#print axioms shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
#print axioms shiftedLaplaceWeightedTerm_holomorphicAt_of_shiftedSqrt

end

end RHFormalization
