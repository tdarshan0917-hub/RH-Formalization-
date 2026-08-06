import RHFormalization.QuadWordTPairedTraceBound
import RHFormalization.HeatSumSqrtBound

/-!
# RHFormalization.OneLetterTPairedTraceBound
**Item 4a part 1: the one-letter T-paired trace bound.**
The word is `(−V)·e^{−u(K+V)}` (one V, ℓ²-norm ≤ SupV via the banked
sublemmas); paired with `D(t−u)` and `T_a` exactly as in item 3b:
`|Tr(D(t−u)·(−V)·e^{−u(K+V)}·T_a)| ≤ (Σ heatWeight)·SupV·√2`, and the
√-variant. Feeds the Duhamel-remainder side of the perturbed spike
kernel bound (4a part 2).
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

/-- The one-letter word `(−V)·e^{−u(K+V)}` as a named matrix. -/
noncomputable def oneWordMatrix (qs : Finset ℕ) (u : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (-(galerkinV (N := N) 1 qs ppWeightReal 1))
    * NormedSpace.exp (u • -(galerkinK (N := N) 1
        + galerkinV (N := N) 1 qs ppWeightReal 1))

/-- One-letter ℓ² engine: `Σ (Mv)² ≤ SupV²·Σ v²`. -/
theorem oneWord_mulVec_sumSq_le (qs : Finset ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 0 ≤ u) (x : Fin N → ℝ) :
    ∑ i : Fin N, (((oneWordMatrix (N := N) qs u).mulVec x) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (x i) ^ 2 := by
  have hV : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n * galerkinV (N := N) 1 qs ppWeightReal 1 m n :=
    fun v => galerkinV_form_nonneg_L 1 one_pos qs v
  have hpeel : (oneWordMatrix (N := N) qs u).mulVec x
      = (-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec
          ((NormedSpace.exp (u • -(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1))).mulVec x) := by
    unfold oneWordMatrix
    rw [← Matrix.mulVec_mulVec]
  rw [hpeel]
  set x2 : Fin N → ℝ :=
    (NormedSpace.exp (u • -(galerkinK (N := N) 1
      + galerkinV (N := N) 1 qs ppWeightReal 1))).mulVec x with hx2
  have h2 : ∑ i : Fin N, (x2 i) ^ 2 ≤ ∑ i : Fin N, (x i) ^ 2 := by
    rw [hx2]
    exact galerkinPerturbedExp_mulVec_sumSq_le 1 qs ppWeightReal 1 hN hV x hu
  have h3 : ∑ i : Fin N,
      (((-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec x2) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (x2 i) ^ 2 := by
    rw [neg_mulVec_eq]
    rw [show (∑ i : Fin N,
        ((-(galerkinV (N := N) 1 qs ppWeightReal 1).mulVec x2) i) ^ 2)
      = ∑ i : Fin N,
          (((galerkinV (N := N) 1 qs ppWeightReal 1).mulVec x2) i) ^ 2
      from sumSq_neg _]
    exact galerkinV_mulVec_sumSq_le qs x2
  calc ∑ i : Fin N,
        (((-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec x2) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (x2 i) ^ 2 := h3
    _ ≤ SupVConst ^ 2 * ∑ i : Fin N, (x i) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- Per-entry: `|(M·T_a) m m| ≤ SupV·√2` for the one-letter word. -/
theorem oneWord_mul_T_diag_abs_le (qs : Finset ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 0 ≤ u) (a : ℝ) (m : Fin N) :
    |(oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a) m m|
      ≤ SupVConst * Real.sqrt 2 := by
  set M : Matrix (Fin N) (Fin N) ℝ := oneWordMatrix (N := N) qs u with hM
  set col : Fin N → ℝ := fun k => galerkinT (N := N) 1 a k m with hcol
  have hcolSq : ∑ k : Fin N, col k ^ 2 ≤ 2 := galerkinT_column_sumSq_le a m
  have hentry : (M * galerkinT (N := N) 1 a) m m = (M.mulVec col) m :=
    mul_diag_eq_mulVec_col M (galerkinT (N := N) 1 a) m
  have hcoord : ((M.mulVec col) m) ^ 2 ≤ ∑ i : Fin N, ((M.mulVec col) i) ^ 2 :=
    sq_coord_le_sumSq (M.mulVec col) m
  have hword : ∑ i : Fin N, ((M.mulVec col) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (col i) ^ 2 := by
    rw [hM]
    exact oneWord_mulVec_sumSq_le qs hN hu col
  have hSnn : 0 ≤ SupVConst := SupVConst_nonneg_adm
  have hsq : ((M * galerkinT (N := N) 1 a) m m) ^ 2
      ≤ SupVConst ^ 2 * 2 := by
    rw [hentry]
    refine le_trans hcoord (le_trans hword ?_)
    nlinarith [hcolSq, sq_nonneg SupVConst]
  have habs2 : |(M * galerkinT (N := N) 1 a) m m| ^ 2
      ≤ (SupVConst * Real.sqrt 2) ^ 2 := by
    rw [sq_abs]
    have h2 : (SupVConst * Real.sqrt 2) ^ 2 = SupVConst ^ 2 * 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2]
    exact hsq
  have hroot := Real.sqrt_le_sqrt habs2
  rw [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (by positivity)] at hroot
  exact hroot

#print axioms oneWordMatrix
#print axioms oneWord_mulVec_sumSq_le
#print axioms oneWord_mul_T_diag_abs_le

end

end RHFormalization
