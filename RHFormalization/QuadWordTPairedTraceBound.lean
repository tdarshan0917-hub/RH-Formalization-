import RHFormalization.QuadDiagonalChainBound
import RHFormalization.GalerkinTColumnBessel

/-!
# RHFormalization.QuadWordTPairedTraceBound
**Ledger item 3b: the T-paired quadratic-word trace bound.**
`|Tr(D_{heatWeight(t−u)}·M·T_a)| ≤ (Σ heatWeight)·(SupV²·√2)`, N-free
constants: diagonal extraction (diag-closer skeleton) + per-entry CS via
the quad-word ℓ² engine (`quadWord_mulVec_sumSq_le`) fed the T-column,
whose sumSq ≤ 2 is item 3a.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Matrix Real

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Product diagonal entry = mulVec of the right factor's column. -/
theorem mul_diag_eq_mulVec_col (M T : Matrix (Fin N) (Fin N) ℝ) (m : Fin N) :
    (M * T) m m = (M.mulVec (fun k => T k m)) m := by
  first
    | simp [Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct]
    | simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The quadratic word (V-sandwich), as a named matrix. -/
noncomputable def quadWordMatrix (qs : Finset ℕ) (u s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (-(galerkinV (N := N) 1 qs ppWeightReal 1))
    * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * NormedSpace.exp (s • -(galerkinK (N := N) 1
            + galerkinV (N := N) 1 qs ppWeightReal 1)))

/-- Per-entry bound: `|(M·T_a) m m| ≤ SupV²·√2` for the quad word M. -/
theorem quadWord_mul_T_diag_abs_le (qs : Finset ℕ) (hN : 0 < N)
    {u s : ℝ} (hus : 0 ≤ u - s) (hs : 0 ≤ s) (a : ℝ) (m : Fin N) :
    |(quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a) m m|
      ≤ SupVConst ^ 2 * Real.sqrt 2 := by
  have hMdef : quadWordMatrix (N := N) qs u s
      = (-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1))) := rfl
  set M : Matrix (Fin N) (Fin N) ℝ :=
    (-(galerkinV (N := N) 1 qs ppWeightReal 1))
      * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * NormedSpace.exp (s • -(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1))) with hM
  set col : Fin N → ℝ := fun k => galerkinT (N := N) 1 a k m with hcol
  have hcolSq : ∑ k : Fin N, col k ^ 2 ≤ 2 := galerkinT_column_sumSq_le a m
  have hMM : quadWordMatrix (N := N) qs u s = M := by rw [hMdef]
  rw [hMM]
  have hentry : (M * galerkinT (N := N) 1 a) m m = (M.mulVec col) m :=
    mul_diag_eq_mulVec_col M (galerkinT (N := N) 1 a) m
  have hcoord : ((M.mulVec col) m) ^ 2 ≤ ∑ i : Fin N, ((M.mulVec col) i) ^ 2 :=
    sq_coord_le_sumSq (M.mulVec col) m
  have hword : ∑ i : Fin N, ((M.mulVec col) i) ^ 2
      ≤ SupVConst ^ 2 * (SupVConst ^ 2 * ∑ i : Fin N, (col i) ^ 2) := by
    rw [hM]
    exact quadWord_mulVec_sumSq_le qs hN hus hs col
  have hsq : ((M * galerkinT (N := N) 1 a) m m) ^ 2
      ≤ (SupVConst ^ 2) ^ 2 * 2 := by
    rw [hentry]
    refine le_trans hcoord (le_trans hword ?_)
    have hS4 : (0:ℝ) ≤ SupVConst ^ 2 := sq_nonneg _
    nlinarith [hcolSq, sq_nonneg SupVConst]
  have habs2 : |(M * galerkinT (N := N) 1 a) m m| ^ 2
      ≤ (SupVConst ^ 2 * Real.sqrt 2) ^ 2 := by
    rw [sq_abs]
    have h2 : (SupVConst ^ 2 * Real.sqrt 2) ^ 2
        = (SupVConst ^ 2) ^ 2 * 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2]
    exact hsq
  have hroot := Real.sqrt_le_sqrt habs2
  rw [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (by positivity)] at hroot
  exact hroot

/-- **Item 3b: the T-paired quad-word trace bound.** N-free, s-free. -/
theorem quadWord_T_trace_le (qs : Finset ℕ) (hN : 0 < N)
    (t u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (hut : u < t) (a : ℝ) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * ((-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
                * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
                * NormedSpace.exp (s • -(galerkinK (N := N) 1
                    + galerkinV (N := N) 1 qs ppWeightReal 1)))
            * galerkinT (N := N) 1 a)).trace|
      ≤ (1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)))⁻¹
          * (SupVConst ^ 2 * Real.sqrt 2) := by
  have hd : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 (t - u) m := by
    intro m
    unfold heatWeight
    exact le_of_lt (Real.exp_pos _)
  set W : Matrix (Fin N) (Fin N) ℝ :=
    (-(galerkinV (N := N) 1 qs ppWeightReal 1))
      * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * NormedSpace.exp (s • -(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1)))
      * galerkinT (N := N) 1 a with hW
  have hWdiag : ∀ m : Fin N, |W m m| ≤ SupVConst ^ 2 * Real.sqrt 2 := by
    intro m
    rw [hW]
    have hform : (-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1)))
        * galerkinT (N := N) 1 a
        = quadWordMatrix (N := N) qs u s * galerkinT (N := N) 1 a := rfl
    rw [hform]
    exact quadWord_mul_T_diag_abs_le qs hN
      (by linarith : (0:ℝ) ≤ u - s) hs a m
  have hsum := sum_heatWeight_le (N := N) 1 one_pos (t - u)
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
    _ ≤ (1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)))⁻¹
          * (SupVConst ^ 2 * Real.sqrt 2) := by
        apply mul_le_mul_of_nonneg_right hsum
        positivity

#print axioms mul_diag_eq_mulVec_col
#print axioms quadWord_mul_T_diag_abs_le
#print axioms quadWord_T_trace_le

end

end RHFormalization
