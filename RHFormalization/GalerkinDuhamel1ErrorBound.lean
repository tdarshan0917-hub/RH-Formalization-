import RHFormalization.GalerkinSpikeErrorBound
import Mathlib

/-!
# Order-1 Duhamel spike error bound

This file lifts the finite spike-sum error bound back to the genuine
order-1 Galerkin Duhamel integrand.

Important normalization:
`duhamel1Integrand_eq_finite_spike_sum` carries the density/window prefactor
`2 / L`.  Therefore the heat-kernel comparison must compare against

  (2 / L) * ∑ q, w q * heatKernelRealScalar t (log q),

and the error bound carries a factor `|2 / L|`.

This fixes the previous mismatch where the finite side was scaled but the
heat-kernel side was not.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/--
The genuine order-1 Duhamel integrand differs from the correctly scaled
B-side Gaussian spike sum by at most `|2/L|` times the weighted finite-spike
error.
-/
theorem abs_duhamel1Integrand_sub_heatKernel_sum_le
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    |duhamel1Integrand (N := N) δ qs w L t u
      -
      (2 / L) * (∑ q ∈ qs, w q * heatKernelRealScalar t (Real.log q))|
      ≤
      |2 / L| *
        (∑ q ∈ qs,
          |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t) := by
  rw [duhamel1Integrand_eq_finite_spike_sum]

  let A : ℝ := 2 / L
  let Sf : ℝ :=
    ∑ q ∈ qs, w q * finiteGalerkinSpikeKernel (N := N) δ q L t
  let Sh : ℝ :=
    ∑ q ∈ qs, w q * heatKernelRealScalar t (Real.log q)

  have hbase :
      |Sf - Sh| ≤
        ∑ q ∈ qs,
          |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t := by
    dsimp [Sf, Sh]
    exact abs_weighted_finiteSpike_sum_sub_heatKernel_sum_le
      (N := N) δ qs w L t

  change |A * Sf - A * Sh| ≤
      |A| *
        (∑ q ∈ qs,
          |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t)

  calc
    |A * Sf - A * Sh|
        = |A| * |Sf - Sh| := by
          rw [← mul_sub, abs_mul]
    _ ≤ |A| *
        (∑ q ∈ qs,
          |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t) := by
          exact mul_le_mul_of_nonneg_left hbase (abs_nonneg A)

/--
Shifted scalar version: multiplying by the Laplace/shift decay factor preserves
the correctly scaled error bound.
-/
theorem abs_shifted_duhamel1Integrand_sub_heatKernel_sum_le
    (σ : ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    |(Real.exp (-σ * t) * Real.exp (-t / 4))
      *
      (duhamel1Integrand (N := N) δ qs w L t u
        -
        (2 / L) * (∑ q ∈ qs, w q * heatKernelRealScalar t (Real.log q)))|
      ≤
      (Real.exp (-σ * t) * Real.exp (-t / 4))
        *
        (|2 / L| *
          (∑ q ∈ qs,
            |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t)) := by
  have hbase :=
    abs_duhamel1Integrand_sub_heatKernel_sum_le
      (N := N) δ qs w L t u
  let A : ℝ := Real.exp (-σ * t) * Real.exp (-t / 4)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact le_of_lt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  calc
    |A *
      (duhamel1Integrand (N := N) δ qs w L t u
        -
        (2 / L) * (∑ q ∈ qs, w q * heatKernelRealScalar t (Real.log q)))|
        =
      A *
      |duhamel1Integrand (N := N) δ qs w L t u
        -
        (2 / L) * (∑ q ∈ qs, w q * heatKernelRealScalar t (Real.log q))| := by
        rw [abs_mul, abs_of_nonneg hA_nonneg]
    _ ≤
      A *
        (|2 / L| *
          (∑ q ∈ qs,
            |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t)) := by
        exact mul_le_mul_of_nonneg_left hbase hA_nonneg

#print axioms abs_duhamel1Integrand_sub_heatKernel_sum_le
#print axioms abs_shifted_duhamel1Integrand_sub_heatKernel_sum_le

end
end RHFormalization
