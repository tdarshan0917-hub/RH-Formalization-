import RHFormalization.QuadWordTPairedTraceBound
import RHFormalization.HeatSumSqrtBound
import RHFormalization.ShortTimeQuadMass

/-!
# RHFormalization.QuadWordTPairedSqrtMass
**Ledger item 3c (part 1): the √-variant T-paired trace bound and the
integral-commutation bridge.** Two theorems:
1. `quadWord_T_trace_sqrt_le` — 3b's bound with the √ heat-sum donor:
   `|Tr(D·M·T_a)| ≤ (√(π/((t−u)·π²))/2)·SupV²·√2`.
2. `duhamel_T_integral_comm` — right-multiplication by `T_a` commutes
   with the inner s-integral (CLM `integral_comp_comm`, the
   `trace_duhamel_integral_comm` template with `mulRight`).
DOWNSTREAM: the T-paired mass function and its `t^{3/2}` bound (part 2),
then the Γ(5/2) transform, then the q-sum (3d).
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

/-- **√-variant of item 3b**: the T-paired trace with heat √-decay. -/
theorem quadWord_T_trace_sqrt_le (qs : Finset ℕ) (hN : 0 < N)
    (t u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (hut : u < t) (a : ℝ) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)).trace|
      ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst ^ 2 * Real.sqrt 2) := by
  have hd : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 (t - u) m := by
    intro m
    unfold heatWeight
    exact le_of_lt (Real.exp_pos _)
  set W : Matrix (Fin N) (Fin N) ℝ :=
    quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a with hW
  have hWdiag : ∀ m : Fin N, |W m m| ≤ SupVConst ^ 2 * Real.sqrt 2 := by
    intro m
    rw [hW]
    exact quadWord_mul_T_diag_abs_le qs hN
      (by linarith : (0:ℝ) ≤ u - s) hs a m
  have hsum := sum_heatWeight_le_sqrt (N := N) 1 one_pos (t - u)
    (by linarith : (0:ℝ) < t - u)
  calc |Matrix.trace ((Matrix.diagonal
          fun m => heatWeight (N := N) 1 (t - u) m) * W)|
      ≤ ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * |W m m| := by
        rw [show Matrix.trace ((Matrix.diagonal
            fun m => heatWeight (N := N) 1 (t - u) m) * W)
          = ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * W m m from by
          unfold Matrix.trace
          rw [show Matrix.diag ((Matrix.diagonal
              fun m => heatWeight (N := N) 1 (t - u) m) * W)
            = fun m => heatWeight (N := N) 1 (t - u) m * W m m from by
            funext m
            first
              | simp [Matrix.diag_apply, Matrix.mul_apply,
                  Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq,
                  Finset.mem_univ]
              | simp [Matrix.diag_apply, Matrix.mul_apply,
                  Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq',
                  Finset.mem_univ]]]
        calc |∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * W m m|
            ≤ ∑ m : Fin N, |heatWeight (N := N) 1 (t - u) m * W m m| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * |W m m| := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [abs_mul, abs_of_nonneg (hd m)]
    _ ≤ ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m
          * (SupVConst ^ 2 * Real.sqrt 2) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact mul_le_mul_of_nonneg_left (hWdiag m) (hd m)
    _ = (∑ m : Fin N, heatWeight (N := N) 1 (t - u) m)
          * (SupVConst ^ 2 * Real.sqrt 2) := by
        rw [← Finset.sum_mul]
    _ ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst ^ 2 * Real.sqrt 2) := by
        apply mul_le_mul_of_nonneg_right hsum
        positivity

/-- Right-multiplication by a fixed matrix commutes with the interval
integral (finite-dimensional CLM). -/
theorem integral_mul_matrix_right (F : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (T : Matrix (Fin N) (Fin N) ℝ) (u v : ℝ)
    (hF : IntervalIntegrable F MeasureTheory.volume u v) :
    (∫ s in u..v, F s) * T = ∫ s in u..v, F s * T := by
  have h := (ContinuousLinearMap.intervalIntegral_comp_comm
    (LinearMap.mulRight ℝ T).toContinuousLinearMap hF).symm
  simpa [LinearMap.mulRight_apply] using h

#print axioms quadWord_T_trace_sqrt_le
#print axioms integral_mul_matrix_right

end

end RHFormalization
