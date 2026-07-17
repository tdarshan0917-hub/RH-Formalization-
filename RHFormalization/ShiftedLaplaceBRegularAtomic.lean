import RHFormalization.ShiftedLaplaceRegularFromZeroDensity

/-!
# RHFormalization.ShiftedLaplaceBRegularAtomic

Atomic analytic step toward shifted/Laplace `hB_regular`.

This version avoids the recurring sign-normal-form mismatch by proving explicit
function equalities and rewriting with them. The issue was not mathematics; Lean
was not identifying

  ((fun _ => -a) * shiftedLaplaceSqrt)

with

  fun s => -(a * shiftedLaplaceSqrt s)

inside `HolomorphicAtC`.
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

  have h_den0 :
      HolomorphicAtC
        (((fun _ : ℂ => (2 : ℂ)) * shiftedLaplaceSqrt))
        z := by
    exact h_two.mul h_sqrt

  have h_den_fun :
      (((fun _ : ℂ => (2 : ℂ)) * shiftedLaplaceSqrt))
        =
      (fun s : ℂ => (2 : ℂ) * shiftedLaplaceSqrt s) := by
    funext s
    rfl

  have h_den :
      HolomorphicAtC
        (fun s : ℂ => (2 : ℂ) * shiftedLaplaceSqrt s)
        z := by
    rw [← h_den_fun]
    exact h_den0

  have h_inv :
      HolomorphicAtC
        (fun s : ℂ => ((2 : ℂ) * shiftedLaplaceSqrt s)⁻¹)
        z := by
    exact h_den.inv hden_ne

  have h_frac_fun :
      (fun s : ℂ => (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s))
        =
      (fun s : ℂ => ((2 : ℂ) * shiftedLaplaceSqrt s)⁻¹) := by
    funext s
    simp [one_div]

  have h_frac :
      HolomorphicAtC
        (fun s : ℂ => (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s))
        z := by
    rw [h_frac_fun]
    exact h_inv

  have h_neg_a :
      HolomorphicAtC (fun _ : ℂ => (-(a : ℂ))) z := by
    exact analyticAt_const

  have h_arg0 :
      HolomorphicAtC
        (((fun _ : ℂ => (-(a : ℂ))) * shiftedLaplaceSqrt))
        z := by
    exact h_neg_a.mul h_sqrt

  have h_arg_fun :
      (((fun _ : ℂ => (-(a : ℂ))) * shiftedLaplaceSqrt))
        =
      (fun s : ℂ => -((a : ℂ) * shiftedLaplaceSqrt s)) := by
    funext s
    simp [Pi.mul_apply]

  have h_arg :
      HolomorphicAtC
        (fun s : ℂ => -((a : ℂ) * shiftedLaplaceSqrt s))
        z := by
    rw [← h_arg_fun]
    exact h_arg0

  have h_exp :
      HolomorphicAtC
        (fun s : ℂ =>
          Complex.exp (-((a : ℂ) * shiftedLaplaceSqrt s)))
        z := by
    exact h_arg.cexp

  have h_prod0 :
      HolomorphicAtC
        (((fun s : ℂ =>
            (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s))
          *
          (fun s : ℂ =>
            Complex.exp (-((a : ℂ) * shiftedLaplaceSqrt s)))))
        z := by
    exact h_frac.mul h_exp

  have h_prod_fun :
      (((fun s : ℂ =>
            (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s))
          *
          (fun s : ℂ =>
            Complex.exp (-((a : ℂ) * shiftedLaplaceSqrt s)))))
        =
      (fun s : ℂ =>
        (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s) *
          Complex.exp (-((a : ℂ) * shiftedLaplaceSqrt s))) := by
    funext s
    rfl

  have h_prod :
      HolomorphicAtC
        (fun s : ℂ =>
          (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s) *
            Complex.exp (-((a : ℂ) * shiftedLaplaceSqrt s)))
        z := by
    rw [← h_prod_fun]
    exact h_prod0

  have h_kernel_fun :
      (fun s : ℂ => shiftedLaplaceHeatKernelC a s)
        =
      (fun s : ℂ =>
        (1 : ℂ) / ((2 : ℂ) * shiftedLaplaceSqrt s) *
          Complex.exp (-((a : ℂ) * shiftedLaplaceSqrt s))) := by
    funext s
    simp [shiftedLaplaceHeatKernelC, shiftedLaplaceSqrt, Pi.mul_apply, neg_mul]

  rw [h_kernel_fun]
  exact h_prod

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

  have h_weighted0 :
      HolomorphicAtC
        (((fun _ : ℂ => q.weightC)
          *
          (fun s : ℂ => shiftedLaplaceHeatKernelC q.center s)))
        z := by
    exact h_const.mul h_kernel

  have h_weighted_fun :
      (((fun _ : ℂ => q.weightC)
          *
          (fun s : ℂ => shiftedLaplaceHeatKernelC q.center s)))
        =
      (fun s : ℂ => q.weightC * shiftedLaplaceHeatKernelC q.center s) := by
    funext s
    rfl

  rw [← h_weighted_fun]
  exact h_weighted0

#print axioms shiftedLaplaceSqrt
#print axioms shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt
#print axioms shiftedLaplaceWeightedTerm_holomorphicAt_of_shiftedSqrt

end

end RHFormalization
