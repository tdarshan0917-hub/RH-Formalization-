import RHFormalization.QuadWordTPairedSqrtMass

/-!
# RHFormalization.QuadTPairedShortTimeMass
**Ledger item 3c part 2: the T-paired short-time mass bound.**
`quadTraceTFn` (the T-paired mirror of `quadTraceFn`) obeys the pointwise
u-simplex bound via part 1, and its `(0,t]` mass obeys the same `t·√t`
bound as the un-paired twin with constant `√2·SupV²/√π`.
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

/-- The T-paired quadratic trace function (mirror of `quadTraceFn`). -/
noncomputable def quadTraceTFn (qs : Finset ℕ) (a t u : ℝ) : ℝ :=
  |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
      * ((∫ s in (0:ℝ)..u, quadWordMatrix (N := N) qs u s)
          * galerkinT (N := N) 1 a)).trace|

theorem quadWordMatrix_continuous (qs : Finset ℕ) (u : ℝ) :
    Continuous (fun s : ℝ => quadWordMatrix (N := N) qs u s) := by
  unfold quadWordMatrix
  fun_prop

/-- **Pointwise bound**: `quadTraceTFn ≤ u·(√(π/((t−u)π²))/2)·SupV²·√2`. -/
theorem quadTraceTFn_le (qs : Finset ℕ) (hN : 0 < N)
    (a t u : ℝ) (hu : 0 ≤ u) (hut : u < t) :
    quadTraceTFn (N := N) qs a t u
      ≤ u * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst ^ 2 * Real.sqrt 2)) := by
  unfold quadTraceTFn
  have hFI : IntervalIntegrable (fun s => quadWordMatrix (N := N) qs u s)
      MeasureTheory.volume 0 u :=
    (quadWordMatrix_continuous qs u).intervalIntegrable 0 u
  rw [integral_mul_matrix_right _ _ _ _ hFI]
  have hFTI : IntervalIntegrable
      (fun s => quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)
      MeasureTheory.volume 0 u :=
    ((quadWordMatrix_continuous qs u).mul continuous_const).intervalIntegrable 0 u
  have hint : (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (∫ s in (0:ℝ)..u,
            quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)
      = ∫ s in (0:ℝ)..u,
          (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
            * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a) := by
    have h := (ContinuousLinearMap.intervalIntegral_comp_comm
      (LinearMap.mulLeft ℝ (Matrix.diagonal
        fun m => heatWeight (N := N) 1 (t - u) m)).toContinuousLinearMap
      hFTI).symm
    simpa [LinearMap.mulLeft_apply] using h
  rw [hint]
  have hDI : IntervalIntegrable
      (fun s => (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a))
      MeasureTheory.volume 0 u :=
    (continuous_const.mul ((quadWordMatrix_continuous qs u).mul
      continuous_const)).intervalIntegrable 0 u
  have htr : (∫ s in (0:ℝ)..u,
        (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)).trace
      = ∫ s in (0:ℝ)..u,
          ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
            * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)).trace := by
    have h := (ContinuousLinearMap.intervalIntegral_comp_comm
      (LinearMap.toContinuousLinearMap
        (Matrix.traceLinearMap (Fin N) ℝ ℝ)) hDI).symm
    simpa using h
  rw [htr]
  have hbound : ∀ s ∈ Set.uIoc (0:ℝ) u,
      ‖((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)).trace‖
        ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
            * (SupVConst ^ 2 * Real.sqrt 2) := by
    intro s hs
    have hsIcc : s ∈ Set.uIcc (0:ℝ) u := Set.uIoc_subset_uIcc hs
    rw [Set.uIcc_of_le hu] at hsIcc
    rw [Real.norm_eq_abs]
    exact quadWord_T_trace_sqrt_le qs hN t u s hsIcc.1 hsIcc.2 hut a
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h
  calc |∫ s in (0:ℝ)..u,
        ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a)).trace|
      ≤ ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst ^ 2 * Real.sqrt 2)) * |u - 0| := h
    _ = u * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * (SupVConst ^ 2 * Real.sqrt 2)) := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - 0)]
        ring

#print axioms quadTraceTFn
#print axioms quadTraceTFn_le

end

end RHFormalization
