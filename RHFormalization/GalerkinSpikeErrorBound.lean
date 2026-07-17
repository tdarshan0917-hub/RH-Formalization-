import RHFormalization.GalerkinDuhamel1HeatKernelTrace
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import Mathlib

/-!
# Galerkin finite spike error bound

This file deliberately does NOT assert the false finite identity

  finiteGalerkinSpikeKernel = heatKernelG.

At finite `N,L`, the Dirichlet heat kernel is not the whole-line Gaussian.
Instead we package the difference as an explicit error term that can be folded
into the residual `R_stage = F_stage - B_stage`.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- Pointwise finite Galerkin spike-vs-Gaussian scalar error. -/
noncomputable def finiteSpikeKernelErrorBound
    (δ : ℝ) (q : ℕ) (L : ℝ) (t : ℝ) : ℝ :=
  |finiteGalerkinSpikeKernel (N := N) δ q L t
    - heatKernelRealScalar t (Real.log q)|

/-- The finite spike-vs-Gaussian difference is bounded by its explicit error term. -/
theorem abs_finiteSpikeKernel_sub_heatKernelRealScalar_le_errorBound
    (δ : ℝ) (q : ℕ) (L : ℝ) (t : ℝ) :
    |finiteGalerkinSpikeKernel (N := N) δ q L t
      - heatKernelRealScalar t (Real.log q)|
      ≤ finiteSpikeKernelErrorBound (N := N) δ q L t := by
  unfold finiteSpikeKernelErrorBound
  exact le_rfl

/--
Weighted finite spike-sum error bound.

This is the safe replacement for the false exact identity:
the weighted finite Galerkin spike sum differs from the weighted B-side Gaussian
sum by at most the weighted sum of explicit finite errors.
-/
theorem abs_weighted_finiteSpike_sum_sub_heatKernel_sum_le
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    |(∑ q ∈ qs,
        w q * finiteGalerkinSpikeKernel (N := N) δ q L t)
      -
      (∑ q ∈ qs,
        w q * heatKernelRealScalar t (Real.log q))|
      ≤
      ∑ q ∈ qs,
        |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t := by
  classical
  let F : ℕ → ℝ := fun q =>
    finiteGalerkinSpikeKernel (N := N) δ q L t
  let G : ℕ → ℝ := fun q =>
    heatKernelRealScalar t (Real.log q)
  let E : ℕ → ℝ := fun q =>
    finiteSpikeKernelErrorBound (N := N) δ q L t
  change
    |(∑ q ∈ qs, w q * F q) - (∑ q ∈ qs, w q * G q)|
      ≤ ∑ q ∈ qs, |w q| * E q
  have hsum :
      (∑ q ∈ qs, w q * F q) - (∑ q ∈ qs, w q * G q)
        = ∑ q ∈ qs, w q * (F q - G q) := by
    calc
      (∑ q ∈ qs, w q * F q) - (∑ q ∈ qs, w q * G q)
          = ∑ q ∈ qs, (w q * F q - w q * G q) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ q ∈ qs, w q * (F q - G q) := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
  rw [hsum]
  calc
    |∑ q ∈ qs, w q * (F q - G q)|
        ≤ ∑ q ∈ qs, |w q * (F q - G q)| := by
          exact Finset.abs_sum_le_sum_abs (fun q => w q * (F q - G q)) qs
    _ = ∑ q ∈ qs, |w q| * E q := by
          apply Finset.sum_congr rfl
          intro q hq
          dsimp [E, F, G, finiteSpikeKernelErrorBound]
          rw [abs_mul]

#print axioms finiteSpikeKernelErrorBound
#print axioms abs_finiteSpikeKernel_sub_heatKernelRealScalar_le_errorBound
#print axioms abs_weighted_finiteSpike_sum_sub_heatKernel_sum_le

end
end RHFormalization
