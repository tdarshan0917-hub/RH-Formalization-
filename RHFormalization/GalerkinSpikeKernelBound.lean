import RHFormalization.GalerkinDuhamel1FiniteSpikeKernel
import RHFormalization.VMatrixElementBound
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
# Bound on the finite Galerkin spike kernel

`finiteGalerkinSpikeKernel q t = ∑_m heatWeight(t)_m · bumpMatrixElement(q,m,m)`.
Each `|bumpMatrixElement| ≤ bumpMass` (banked) and `heatWeight ≥ 0`, so

  |finiteGalerkinSpikeKernel q t| ≤ bumpMass q · ∑_m heatWeight(t)_m.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- `heatWeight` is nonnegative (it is an exponential). -/
theorem heatWeight_nonneg (L : ℝ) (t : ℝ) (m : Fin N) :
    0 ≤ heatWeight (N := N) L t m := by
  unfold heatWeight; exact le_of_lt (Real.exp_pos _)

/-- **Spike-kernel bound.** `|finiteGalerkinSpikeKernel q t| ≤ bumpMass q · ∑_m heatWeight(t)_m`. -/
theorem abs_finiteGalerkinSpikeKernel_le
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) (t : ℝ) :
    |finiteGalerkinSpikeKernel (N := N) δ q L t|
      ≤ bumpMass δ q L * ∑ m : Fin N, heatWeight (N := N) L t m := by
  unfold finiteGalerkinSpikeKernel
  calc |∑ m : Fin N, heatWeight (N := N) L t m * bumpMatrixElement δ q L (m + 1) (m + 1)|
      ≤ ∑ m : Fin N, |heatWeight (N := N) L t m * bumpMatrixElement δ q L (m + 1) (m + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m : Fin N, heatWeight (N := N) L t m * |bumpMatrixElement δ q L (m + 1) (m + 1)| := by
        apply Finset.sum_congr rfl; intro m _
        rw [abs_mul, abs_of_nonneg (heatWeight_nonneg L t m)]
    _ ≤ ∑ m : Fin N, heatWeight (N := N) L t m * bumpMass δ q L := by
        apply Finset.sum_le_sum; intro m _
        apply mul_le_mul_of_nonneg_left _ (heatWeight_nonneg L t m)
        exact abs_bumpMatrixElement_le_bumpMass δ hδ q L hL (m + 1) (m + 1)
    _ = (∑ m : Fin N, heatWeight (N := N) L t m) * bumpMass δ q L := by
        rw [← Finset.sum_mul]
    _ = bumpMass δ q L * ∑ m : Fin N, heatWeight (N := N) L t m := by
        rw [mul_comm]

#print axioms abs_finiteGalerkinSpikeKernel_le

end
end RHFormalization
