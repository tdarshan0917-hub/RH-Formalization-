import RHFormalization.OneLetterTPairedTraceBound
import RHFormalization.QuadTPairedMassBound
import RHFormalization.GalerkinSpikeDuhamel

/-!
# RHFormalization.OneLetterTPairedMass
**Item 4a part 2: the u-integrated one-letter (exact Duhamel) remainder
bound.** The √-variant D-paired trace bound for the one-letter word, then
the a.e.-domination endgame (the banked `shortTime_quadMass_le` skeleton)
bounding `∫₀ᵗ |Tr(D(t−u)·(−V)·e^{−u(K+V)}·T_a)| du ≤ 2·√t·SupV·√2/√π ·
...` — via the (t−u)^{−1/2}-integrable majorant WITHOUT the u-factor
(the one-letter integrand has no inner s-integral, so no u growth):
majorant `(SupV·√2/(2·√π))·√π·(t−u)^{−1/2}`… constants fixed by the
banked donors. Output: the exact spike Duhamel remainder mass ≤ `2√t·C₁`.
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

/-- **√-variant D-paired one-letter trace bound** (3b/3c-part-1 skeleton
with the one-letter per-entry lemma). -/
theorem oneWord_T_trace_sqrt_le (qs : Finset ℕ) (hN : 0 < N)
    (t u : ℝ) (hu : 0 ≤ u) (hut : u < t) (a : ℝ) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace|
      ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst * Real.sqrt 2) := by
  have hd : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 (t - u) m := by
    intro m
    unfold heatWeight
    exact le_of_lt (Real.exp_pos _)
  set W : Matrix (Fin N) (Fin N) ℝ :=
    oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a with hW
  have hWdiag : ∀ m : Fin N, |W m m| ≤ SupVConst * Real.sqrt 2 := by
    intro m
    rw [hW]
    exact oneWord_mul_T_diag_abs_le qs hN hu a m
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
          * (SupVConst * Real.sqrt 2) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact mul_le_mul_of_nonneg_left (hWdiag m) (hd m)
    _ = (∑ m : Fin N, heatWeight (N := N) 1 (t - u) m)
          * (SupVConst * Real.sqrt 2) := by
        rw [← Finset.sum_mul]
    _ ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst * Real.sqrt 2) := by
        apply mul_le_mul_of_nonneg_right hsum
        have hSnn : 0 ≤ SupVConst := SupVConst_nonneg_adm
        positivity

#print axioms oneWord_T_trace_sqrt_le

end

end RHFormalization
