-- SENTINEL: quad-diagonal-chain-bound-v1
import RHFormalization.QuadRemainderFrobBound
import RHFormalization.SymmFormPolarizationBound
import RHFormalization.GalerkinPerturbedExpContraction
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
# The N-free diagonal chain: short-time quadratic sector closer

`|tr(diag(hw)·M)| ≤ (Σ hw)·SupVConst²` where `M = (−V)·E₁·(−V)·E₂`:
each diagonal entry of `M` is bounded via the unit-vector column chain —
contraction (banked) → polarization ℓ²-bound (banked) → contraction (banked)
→ polarization bound (banked) — with NO dimension factor and NO s-dependence.
Combined with `sum_heatWeight_le` (banked, N-free geometric bound), this is
the manuscript's "form bound controls each insertion, heat factors supply
the trace smoothing", kernel-checked.
DOWNSTREAM CONSUMER: short-time residual local boundedness along α → h_conv.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Diagonal entry as a mulVec coordinate at a unit basis vector. -/
theorem diag_entry_eq_mulVec_unit
    (M : Matrix (Fin N) (Fin N) ℝ) (m : Fin N) :
    M m m = (M.mulVec (fun k => if k = m then (1:ℝ) else 0)) m := by
  first
    | simp [Matrix.mulVec, Matrix.dotProduct, mul_ite, Finset.sum_ite_eq',
        Finset.mem_univ]
    | simp [Matrix.mulVec, dotProduct, mul_ite, Finset.sum_ite_eq',
        Finset.mem_univ]
    | (simp [Matrix.mulVec_single]
       rfl)

/-- Unit basis vector has unit sum of squares. -/
theorem unitVec_sumSq (m : Fin N) :
    ∑ i : Fin N, ((fun k => if k = m then (1:ℝ) else 0) i) ^ 2 = 1 := by
  first
    | simp [apply_ite, Finset.sum_ite_eq', Finset.mem_univ]
    | (rw [Finset.sum_eq_single m]
       · simp
       · intro n _ hnm
         simp [hnm]
       · intro hm
         exact absurd (Finset.mem_univ m) hm)

/-- One coordinate squared is at most the sum of squares. -/
theorem sq_coord_le_sumSq (x : Fin N → ℝ) (m : Fin N) :
    (x m) ^ 2 ≤ ∑ i : Fin N, (x i) ^ 2 :=
  Finset.single_le_sum (f := fun i => (x i) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ m)

/-- mulVec of a negated matrix. -/
theorem neg_mulVec_eq (M : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    (-M).mulVec x = -(M.mulVec x) := by
  first
    | exact Matrix.neg_mulVec M x
    | exact Matrix.neg_mulVec x M
    | (funext i
       simp [Matrix.mulVec, Matrix.dotProduct, Finset.sum_neg_distrib])
    | (funext i
       simp [Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib])

/-- Sum-of-squares is negation invariant. -/
theorem sumSq_neg (x : Fin N → ℝ) :
    ∑ i : Fin N, ((-x) i) ^ 2 = ∑ i : Fin N, (x i) ^ 2 := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.neg_apply, neg_sq]

/-- **The column chain**: ℓ²-mass of `((−V)·E₁·(−V)·E₂)·x` is bounded by
`SupVConst⁴ · Σx²` at the stage parameters. -/
theorem quadWord_mulVec_sumSq_le
    (qs : Finset ℕ) (hN : 0 < N)
    {u s : ℝ} (hus : 0 ≤ u - s) (hs : 0 ≤ s)
    (x : Fin N → ℝ) :
    ∑ i : Fin N,
      ((((-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1)))).mulVec x) i) ^ 2
      ≤ SupVConst ^ 2 * (SupVConst ^ 2 * ∑ i : Fin N, (x i) ^ 2) := by
  have hV : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n * galerkinV (N := N) 1 qs ppWeightReal 1 m n :=
    fun v => galerkinV_form_nonneg_L 1 one_pos qs v
  -- peel the word: (−V) * (E₁ * (−V) * E₂) applied to x
  have hpeel :
      ((-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1)))).mulVec x
      = (-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec
          ((NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)).mulVec
            ((-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec
              ((NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1))).mulVec x))) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hpeel]
  set x2 : Fin N → ℝ :=
    (NormedSpace.exp (s • -(galerkinK (N := N) 1
      + galerkinV (N := N) 1 qs ppWeightReal 1))).mulVec x with hx2
  set x3 : Fin N → ℝ :=
    (-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec x2 with hx3
  set x4 : Fin N → ℝ :=
    (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)).mulVec x3 with hx4
  -- innermost: perturbed contraction
  have h2 : ∑ i : Fin N, (x2 i) ^ 2 ≤ ∑ i : Fin N, (x i) ^ 2 := by
    rw [hx2]
    exact galerkinPerturbedExp_mulVec_sumSq_le 1 qs ppWeightReal 1 hN hV x hs
  -- V insertion (negation absorbed)
  have h3 : ∑ i : Fin N, (x3 i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (x2 i) ^ 2 := by
    rw [hx3, neg_mulVec_eq]
    rw [show (∑ i : Fin N,
        ((-(galerkinV (N := N) 1 qs ppWeightReal 1).mulVec x2) i) ^ 2)
      = ∑ i : Fin N,
          (((galerkinV (N := N) 1 qs ppWeightReal 1).mulVec x2) i) ^ 2
      from sumSq_neg _]
    exact galerkinV_mulVec_sumSq_le qs x2
  -- free contraction
  have h4 : ∑ i : Fin N, (x4 i) ^ 2 ≤ ∑ i : Fin N, (x3 i) ^ 2 := by
    rw [hx4]
    exact galerkinFreeExp_mulVec_sumSq_le 1 hN x3 hus
  -- outermost V insertion
  have h5 : ∑ i : Fin N,
      (((-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec x4) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (x4 i) ^ 2 := by
    rw [neg_mulVec_eq]
    rw [show (∑ i : Fin N,
        ((-(galerkinV (N := N) 1 qs ppWeightReal 1).mulVec x4) i) ^ 2)
      = ∑ i : Fin N,
          (((galerkinV (N := N) 1 qs ppWeightReal 1).mulVec x4) i) ^ 2
      from sumSq_neg _]
    exact galerkinV_mulVec_sumSq_le qs x4
  have hSup2 : (0:ℝ) ≤ SupVConst ^ 2 := sq_nonneg _
  calc ∑ i : Fin N,
        (((-(galerkinV (N := N) 1 qs ppWeightReal 1)).mulVec x4) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (x4 i) ^ 2 := h5
    _ ≤ SupVConst ^ 2 * ∑ i : Fin N, (x3 i) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 hSup2
    _ ≤ SupVConst ^ 2 * (SupVConst ^ 2 * ∑ i : Fin N, (x2 i) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hSup2
    _ ≤ SupVConst ^ 2 * (SupVConst ^ 2 * ∑ i : Fin N, (x i) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hSup2
        exact mul_le_mul_of_nonneg_left h2 hSup2

/-- **THE SECTOR CLOSER.** The quadratic integrand trace is bounded by
`(Σ heatWeight)·SupVConst²` — N-free, s-free, α-uniform. -/
theorem quadIntegrand_trace_diag_le
    (qs : Finset ℕ) (hN : 0 < N)
    (t u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hut : u < t) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1)
            * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
                * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
                * NormedSpace.exp (s • -(galerkinK (N := N) 1
                    + galerkinV (N := N) 1 qs ppWeightReal 1))))).trace|
      ≤ (1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)))⁻¹
          * SupVConst ^ 2 := by
  have hd : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 (t - u) m := by
    intro m
    unfold heatWeight
    exact le_of_lt (Real.exp_pos _)
  set M : Matrix (Fin N) (Fin N) ℝ :=
    (-(galerkinV (N := N) 1 qs ppWeightReal 1)
      * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * NormedSpace.exp (s • -(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1)))) with hM
  have hMdiag : ∀ m : Fin N, |M m m| ≤ SupVConst ^ 2 := by
    intro m
    set e : Fin N → ℝ := (fun k => if k = m then (1:ℝ) else 0) with he
    have hcol := quadWord_mulVec_sumSq_le qs hN
      (by linarith : (0:ℝ) ≤ u - s) hs e
    have hunit : ∑ i : Fin N, (e i) ^ 2 = 1 := by
      rw [he]
      exact unitVec_sumSq m
    rw [hunit, mul_one] at hcol
    have hentry : M m m = (M.mulVec e) m := by
      rw [he]
      exact diag_entry_eq_mulVec_unit M m
    have hcoord : ((M.mulVec e) m) ^ 2 ≤ ∑ i : Fin N, ((M.mulVec e) i) ^ 2 :=
      sq_coord_le_sumSq (M.mulVec e) m
    have hsq : (M m m) ^ 2 ≤ SupVConst ^ 2 * SupVConst ^ 2 := by
      rw [hentry]
      refine le_trans hcoord ?_
      rw [hM]
      exact hcol
    have habs2 : |M m m| ^ 2 ≤ (SupVConst ^ 2) ^ 2 := by
      rw [sq_abs]
      calc (M m m) ^ 2 ≤ SupVConst ^ 2 * SupVConst ^ 2 := hsq
        _ = (SupVConst ^ 2) ^ 2 := by ring
    have hroot := Real.sqrt_le_sqrt habs2
    rw [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (sq_nonneg _)] at hroot
    exact hroot
  have hsum := sum_heatWeight_le (N := N) 1 one_pos (t - u)
    (by linarith : (0:ℝ) < t - u)
  calc |Matrix.trace ((Matrix.diagonal
          fun m => heatWeight (N := N) 1 (t - u) m) * M)|
      ≤ ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * |M m m| := by
        rw [show Matrix.trace ((Matrix.diagonal
            fun m => heatWeight (N := N) 1 (t - u) m) * M)
          = ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * M m m from by
          unfold Matrix.trace
          rw [show Matrix.diag ((Matrix.diagonal
              fun m => heatWeight (N := N) 1 (t - u) m) * M)
            = fun m => heatWeight (N := N) 1 (t - u) m * M m m from by
            funext m
            first
              | simp [Matrix.diag_apply, Matrix.mul_apply,
                  Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq,
                  Finset.mem_univ]
              | simp [Matrix.diag_apply, Matrix.mul_apply,
                  Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq',
                  Finset.mem_univ]]]
        calc |∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * M m m|
            ≤ ∑ m : Fin N, |heatWeight (N := N) 1 (t - u) m * M m m| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * |M m m| := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [abs_mul, abs_of_nonneg (hd m)]
    _ ≤ ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m
          * SupVConst ^ 2 := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact mul_le_mul_of_nonneg_left (hMdiag m) (hd m)
    _ = (∑ m : Fin N, heatWeight (N := N) 1 (t - u) m)
          * SupVConst ^ 2 := by
        rw [← Finset.sum_mul]
    _ ≤ (1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)))⁻¹
          * SupVConst ^ 2 := by
        apply mul_le_mul_of_nonneg_right hsum
        positivity

#print axioms diag_entry_eq_mulVec_unit
#print axioms unitVec_sumSq
#print axioms sq_coord_le_sumSq
#print axioms neg_mulVec_eq
#print axioms sumSq_neg
#print axioms quadWord_mulVec_sumSq_le
#print axioms quadIntegrand_trace_diag_le
