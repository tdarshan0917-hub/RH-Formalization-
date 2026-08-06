import RHFormalization.OneLetterMassBound
import RHFormalization.GalerkinSpikeDuhamel
import RHFormalization.GalerkinFreeHeatDiagonal

/-!
# RHFormalization.PerturbedSpikeKernelBound
**GPT step 3 opener: the perturbed spike kernel triangle bound.**
Two theorems: the free T-paired kernel bound
`|Tr(D(t)·T_a)| ≤ (Σ heatWeight t)·2` (3b trace-extraction skeleton with
the banked entry bound), and the triangle
`|Tr(e^{−t(K+V)}·T_a)| ≤ (Σ heatWeight t)·2 + √t·SupV·√2/√π` via the
banked Duhamel identity + `galerkinFreeHeat_eq_diagonal` +
`oneLetter_mass_le`. N-free, a-free, qs-uniform.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory intervalIntegral

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- **Free T-paired kernel bound**: `|Tr(D(t)·T_a)| ≤ (Σ heatWeight)·2`. -/
theorem free_T_kernel_abs_le (t a : ℝ) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 t m)
        * galerkinT (N := N) 1 a).trace|
      ≤ (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2 := by
  have hd : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 t m := by
    intro m
    unfold heatWeight
    exact le_of_lt (Real.exp_pos _)
  have hWdiag : ∀ m : Fin N, |galerkinT (N := N) 1 a m m| ≤ 2 :=
    fun m => galerkinT_entry_abs_le 1 a one_pos m m
  calc |Matrix.trace ((Matrix.diagonal
          fun m => heatWeight (N := N) 1 t m) * galerkinT (N := N) 1 a)|
      ≤ ∑ m : Fin N, heatWeight (N := N) 1 t m * |galerkinT (N := N) 1 a m m| := by
        rw [show Matrix.trace ((Matrix.diagonal
            fun m => heatWeight (N := N) 1 t m) * galerkinT (N := N) 1 a)
          = ∑ m : Fin N, heatWeight (N := N) 1 t m
              * galerkinT (N := N) 1 a m m from by
          unfold Matrix.trace
          rw [show Matrix.diag ((Matrix.diagonal
              fun m => heatWeight (N := N) 1 t m) * galerkinT (N := N) 1 a)
            = fun m => heatWeight (N := N) 1 t m
                * galerkinT (N := N) 1 a m m from by
            funext m
            first
              | simp [Matrix.diag_apply, Matrix.mul_apply,
                  Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq,
                  Finset.mem_univ]
              | simp [Matrix.diag_apply, Matrix.mul_apply,
                  Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq',
                  Finset.mem_univ]]]
        calc |∑ m : Fin N, heatWeight (N := N) 1 t m
              * galerkinT (N := N) 1 a m m|
            ≤ ∑ m : Fin N, |heatWeight (N := N) 1 t m
                * galerkinT (N := N) 1 a m m| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ m : Fin N, heatWeight (N := N) 1 t m
                * |galerkinT (N := N) 1 a m m| := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [abs_mul, abs_of_nonneg (hd m)]
    _ ≤ ∑ m : Fin N, heatWeight (N := N) 1 t m * 2 := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact mul_le_mul_of_nonneg_left (hWdiag m) (hd m)
    _ = (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2 := by
        rw [← Finset.sum_mul]

/-- **The perturbed spike kernel bound** (triangle via banked Duhamel). -/
theorem perturbedSpikeKernel_abs_le (qs : Finset ℕ) (hN : 0 < N)
    (t a : ℝ) (ht : 0 < t) :
    |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|
      ≤ (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2
        + Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi := by
  rw [galerkinSpikeKernel_duhamel 1 qs ppWeightReal 1 t a]
  refine le_trans (abs_add _ _) (add_le_add ?_ ?_)
  · -- free leg: rewrite the free kernel to D-form, then the bound above
    unfold galerkinSpikeKernel
    rw [galerkinFreeHeat_eq_diagonal (N := N) 1 t]
    exact free_T_kernel_abs_le t a
  · -- remainder leg: rewrite integrand to D·oneWord·T, then mass bound
    have hrw : ∀ u : ℝ,
        (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) 1)))
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * NormedSpace.exp (u • (-(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1)))
          * galerkinT (N := N) 1 a).trace
        = ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
            * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace := by
      intro u
      rw [galerkinFreeHeat_eq_diagonal (N := N) 1 (t - u)]
      unfold oneWordMatrix
      congr 1
      rw [← Matrix.mul_assoc]
    calc |∫ u in (0:ℝ)..t,
          (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) 1)))
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (u • (-(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1)))
            * galerkinT (N := N) 1 a).trace|
        = |∫ u in (0:ℝ)..t,
            ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
              * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace| := by
          congr 1
          exact intervalIntegral.integral_congr (fun u _ => hrw u)
      _ ≤ ∫ u in (0:ℝ)..t,
            |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
              * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace| :=
          intervalIntegral.abs_integral_le_integral_abs ht.le
      _ = ∫ u in (0:ℝ)..t, oneTraceTFn (N := N) qs a t u := by
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          rfl
      _ ≤ Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi :=
          oneLetter_mass_le qs hN a t ht

#print axioms free_T_kernel_abs_le
#print axioms perturbedSpikeKernel_abs_le

end

end RHFormalization
