import RHFormalization.DenseDecodedPotential
import RHFormalization.DenseCenteredObservable
import RHFormalization.DenseGalerkinSchedule
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
B(i)-4 part 2 (GPT FINAL GO, option (a) — genuinely perturbed energy).

1. `denseV_posSemidef` — banked form fact lifted to `Matrix.PosSemidef`.
2. `denseAV n a = diagonal (λ_k + a) + denseV n` (equals aI + diag λ + V;
   combined-diagonal order chosen for the cleaner `PosDef.add_posSemidef`).
3. `denseAV_posDef` for 0 < a.
4. `denseQV n a = (1/2L)·Tr[Cᵀ (A_V)⁻¹ C]` — V INSIDE the resolvent
   (free-resolvent shape rejected by GPT: it would reduce the first CS
   factor to the dead free energy Q⁰).
5. `denseQV_nonneg`.
6–8. Diagonal-trace dual (GPT-signed): `S⁰`, `J^V`, `S^V = S⁰ + J^V` exact,
   and absorption `J^V ≤ (ε_n/a)·S⁰`, `S^V ≤ (1+ε_n/a)·S⁰` with
   `ε_n = denseVrate n = 24(log4+4)(n+2)^{-1/8}` (part-1 rate; = X^{-1/4}).
9. 1/(2L) normalization on BOTH Q^V and S^V (signed: weighted-HS CS then
   gives |τ(D_sC_n)|² ≤ Q^V·S^V with no stray constants — brick 8).

B7 LEDGER CORRECTION (GPT-signed): since B(i)-1 gives 2·densePaired = Pgal
exactly, the LIVE hP_dense bridge identity is
  2·densePaired − M = 2τ(D_sC_n) + F^ctr − E⁰  (F^sp CANCELS here).
F^sp = Pcont − Pgal stays banked but belongs to the Pcont − M identity.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 400000

namespace RHFormalization

noncomputable section

open Matrix Real
open scoped BigOperators

/-- The frozen dense potential entry rate `ε_n = 24(log4+4)·(n+2)^{-1/8}`
(equals `24(log4+4)·X^{-1/4}` in X-variables, X = √(n+2)). -/
noncomputable def denseVrate (n : ℕ) : ℝ :=
  24 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ (-(1:ℝ)/8)

theorem denseVrate_nonneg (n : ℕ) : 0 ≤ denseVrate n := by
  unfold denseVrate
  have hlog : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hr : (0:ℝ) ≤ ((n:ℝ)+2) ^ (-(1:ℝ)/8) :=
    Real.rpow_nonneg (by positivity) _
  have h24 : (0:ℝ) ≤ 24 * (Real.log 4 + 4) := by nlinarith
  exact mul_nonneg h24 hr

/-- Diagonal entries obey the frozen rate. -/
theorem denseV_diag_le_rate (n : ℕ) (k : Fin (denseN n)) :
    denseV n k k ≤ denseVrate n := by
  unfold denseVrate
  exact le_trans (le_abs_self _) (abs_denseV_entry_le_rpow n k k)

/-- **Export 1**: `denseV` is positive semidefinite. -/
theorem denseV_posSemidef (n : ℕ) : (denseV n).PosSemidef := by
  have hherm : (denseV n).IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    rw [star_trivial]
    unfold denseV
    exact decodedGalerkinV_symm 1 _ ppWeightReal (denseL n) j i
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  have hx : star x = x := by
    first
      | exact star_trivial x
      | (funext i; exact star_trivial (x i))
      | simp
  rw [hx]
  have hexpand : x ⬝ᵥ (denseV n *ᵥ x)
      = ∑ m : Fin (denseN n), ∑ j : Fin (denseN n),
          x m * x j * denseV n m j := by
    first
      | (simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
         exact Finset.sum_congr rfl fun m _ =>
           Finset.sum_congr rfl fun j _ => by ring)
      | (simp only [Matrix.dotProduct, Matrix.mulVec, Finset.mul_sum]
         exact Finset.sum_congr rfl fun m _ =>
           Finset.sum_congr rfl fun j _ => by ring)
      | (unfold Matrix.mulVec dotProduct
         simp only [Finset.mul_sum]
         exact Finset.sum_congr rfl fun m _ =>
           Finset.sum_congr rfl fun j _ => by ring)
  rw [hexpand]
  exact denseV_form_nonneg n x

/-- **Export 2**: the perturbed operator `A_V(a) = diag(λ_k + a) + V`
(= aI + diag λ + V; combined diagonal for the cleaner PosDef proof). -/
noncomputable def denseAV (n : ℕ) (a : ℝ) :
    Matrix (Fin (denseN n)) (Fin (denseN n)) ℝ :=
  Matrix.diagonal (fun k : Fin (denseN n) =>
    galerkinLam (denseL n) (k : ℕ) + a) + denseV n

/-- **Export 3**: `A_V(a)` is positive definite for `0 < a`. -/
theorem denseAV_posDef (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (denseAV n a).PosDef := by
  have hdiag : (Matrix.diagonal (fun k : Fin (denseN n) =>
      galerkinLam (denseL n) (k : ℕ) + a)).PosDef := by
    have hpos : ∀ k : Fin (denseN n),
        0 < galerkinLam (denseL n) (k : ℕ) + a :=
      fun k => add_pos_of_nonneg_of_pos (galerkinLam_nonneg _ _) ha
    first
      | exact Matrix.posDef_diagonal_iff.mpr hpos
      | exact Matrix.PosDef.diagonal hpos
  exact hdiag.add_posSemidef (denseV_posSemidef n)

/-- **Export 4 — the genuinely perturbed dense energy** (option (a)):
`Q^V_n(a) = (1/2L)·Tr[Cᵀ (A_V(a))⁻¹ C]`, V inside the resolvent. -/
noncomputable def denseQV (n : ℕ) (a : ℝ) : ℝ :=
  (1 / (2 * denseL n)) *
    ((denseCenteredMatrix n)ᵀ * (denseAV n a)⁻¹ * denseCenteredMatrix n).trace

/-- **Export 5**: `0 ≤ Q^V_n(a)` for `0 < a`. -/
theorem denseQV_nonneg (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 ≤ denseQV n a := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have h2L : (0:ℝ) < 2 * denseL n := by linarith
  have hinv : ((denseAV n a)⁻¹).PosSemidef :=
    (denseAV_posDef n ha).inv.posSemidef
  have hT : (denseCenteredMatrix n)ᴴ = (denseCenteredMatrix n)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hmat : ((denseCenteredMatrix n)ᵀ * (denseAV n a)⁻¹
      * denseCenteredMatrix n).PosSemidef := by
    rw [← hT]
    exact hinv.conjTranspose_mul_mul_same (denseCenteredMatrix n)
  unfold denseQV
  exact mul_nonneg (le_of_lt (one_div_pos.mpr h2L)) hmat.trace_nonneg

/-- **Export 6a**: free dual piece `S⁰_n(a,d) = (1/2L)·Σ (λ_k+a)·d_k²`. -/
noncomputable def denseS0 (n : ℕ) (a : ℝ) (d : Fin (denseN n) → ℝ) : ℝ :=
  (1 / (2 * denseL n)) * ∑ k : Fin (denseN n),
    (galerkinLam (denseL n) (k : ℕ) + a) * d k ^ 2

/-- **Export 6b**: potential dual piece `J^V_n(d) = (1/2L)·Σ d_k²·V_kk`
(diagonal-trace dual object, GPT-signed). -/
noncomputable def denseJV (n : ℕ) (d : Fin (denseN n) → ℝ) : ℝ :=
  (1 / (2 * denseL n)) * ∑ k : Fin (denseN n), d k ^ 2 * denseV n k k

/-- **Export 6c**: full dual `S^V_n(a,d) = S⁰ + J^V`. -/
noncomputable def denseSVReal (n : ℕ) (a : ℝ) (d : Fin (denseN n) → ℝ) : ℝ :=
  denseS0 n a d + denseJV n d

/-- **Export 7 — exact split** (definitional). -/
theorem denseSVReal_eq_S0_add_JV (n : ℕ) (a : ℝ) (d : Fin (denseN n) → ℝ) :
    denseSVReal n a d = denseS0 n a d + denseJV n d := rfl

theorem denseS0_nonneg (n : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (d : Fin (denseN n) → ℝ) : 0 ≤ denseS0 n a d := by
  have h2L : (0:ℝ) < 2 * denseL n := by have := denseL_pos n; linarith
  unfold denseS0
  refine mul_nonneg (le_of_lt (one_div_pos.mpr h2L)) (Finset.sum_nonneg ?_)
  intro k _
  have := galerkinLam_nonneg (denseL n) (k : ℕ)
  exact mul_nonneg (by linarith) (sq_nonneg _)

theorem denseJV_nonneg (n : ℕ) (d : Fin (denseN n) → ℝ) :
    0 ≤ denseJV n d := by
  have h2L : (0:ℝ) < 2 * denseL n := by have := denseL_pos n; linarith
  unfold denseJV
  exact mul_nonneg (le_of_lt (one_div_pos.mpr h2L))
    (Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg _) (denseV_diag_nonneg n k))

/-- **Export 8a — absorption**: `J^V ≤ (ε_n/a)·S⁰` for `0 < a`. -/
theorem denseJV_le_ratio (n : ℕ) {a : ℝ} (ha : 0 < a)
    (d : Fin (denseN n) → ℝ) :
    denseJV n d ≤ (denseVrate n / a) * denseS0 n a d := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have h2L : (0:ℝ) < 2 * denseL n := by linarith
  have hpre : (0:ℝ) ≤ 1 / (2 * denseL n) := le_of_lt (one_div_pos.mpr h2L)
  have hdiv : (0:ℝ) ≤ denseVrate n / a :=
    div_nonneg (denseVrate_nonneg n) ha.le
  unfold denseJV denseS0
  rw [show (denseVrate n / a) * ((1 / (2 * denseL n)) *
        ∑ k : Fin (denseN n), (galerkinLam (denseL n) (k : ℕ) + a) * d k ^ 2)
      = (1 / (2 * denseL n)) * ((denseVrate n / a) *
        ∑ k : Fin (denseN n), (galerkinLam (denseL n) (k : ℕ) + a) * d k ^ 2)
    from by ring]
  refine mul_le_mul_of_nonneg_left ?_ hpre
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro k _
  have hV : denseV n k k ≤ denseVrate n := denseV_diag_le_rate n k
  have hlam : (0:ℝ) ≤ galerkinLam (denseL n) (k : ℕ) :=
    galerkinLam_nonneg _ _
  have h2 : denseVrate n
      ≤ denseVrate n / a * (galerkinLam (denseL n) (k : ℕ) + a) := by
    have hcancel : denseVrate n / a * a = denseVrate n :=
      div_mul_cancel₀ _ (ne_of_gt ha)
    calc denseVrate n = denseVrate n / a * a := hcancel.symm
      _ ≤ denseVrate n / a * (galerkinLam (denseL n) (k : ℕ) + a) := by
          refine mul_le_mul_of_nonneg_left ?_ hdiv
          linarith
  calc d k ^ 2 * denseV n k k
      ≤ d k ^ 2 * denseVrate n :=
        mul_le_mul_of_nonneg_left hV (sq_nonneg _)
    _ ≤ d k ^ 2 * (denseVrate n / a
          * (galerkinLam (denseL n) (k : ℕ) + a)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = denseVrate n / a
          * ((galerkinLam (denseL n) (k : ℕ) + a) * d k ^ 2) := by ring

/-- **Export 8b**: `S^V ≤ (1 + ε_n/a)·S⁰` for `0 < a`. -/
theorem denseSVReal_le (n : ℕ) {a : ℝ} (ha : 0 < a)
    (d : Fin (denseN n) → ℝ) :
    denseSVReal n a d ≤ (1 + denseVrate n / a) * denseS0 n a d := by
  have h1 := denseJV_le_ratio n ha d
  calc denseSVReal n a d
      = denseS0 n a d + denseJV n d := rfl
    _ ≤ denseS0 n a d + denseVrate n / a * denseS0 n a d := by
        linarith
    _ = (1 + denseVrate n / a) * denseS0 n a d := by ring

#print axioms denseVrate_nonneg
#print axioms denseV_diag_le_rate
#print axioms denseV_posSemidef
#print axioms denseAV_posDef
#print axioms denseQV_nonneg
#print axioms denseSVReal_eq_S0_add_JV
#print axioms denseS0_nonneg
#print axioms denseJV_nonneg
#print axioms denseJV_le_ratio
#print axioms denseSVReal_le

end

end RHFormalization
