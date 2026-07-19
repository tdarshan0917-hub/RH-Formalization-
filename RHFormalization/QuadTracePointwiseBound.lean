-- SENTINEL: quad-trace-pointwise-v2
import RHFormalization.FrobExpKVBound
import RHFormalization.GalerkinFullSandwichTraceSplit
import Mathlib

/-! # Core brick 6c-iv-a — pointwise quad-trace bound.
`|Tr(D(t−u)·(−V)·Inner(u))| ≤ N^{5/2}·u·frobSq(V)` via the banked
Frobenius chain (6a, 6c-i, 6c-ii, 6c-iii) + entrywise integral CLM. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Entry evaluation as a continuous linear map (probe-verified pattern). -/
def entryCLM (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem entryCLM_apply (i j : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) :
    entryCLM i j M = M i j := rfl

/-- Entry of an interval integral = interval integral of the entry. -/
theorem integral_entry (a b : ℝ) (F : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hF : Continuous F) (i j : Fin N) :
    (∫ u in a..b, F u) i j = ∫ u in a..b, (F u) i j := by
  have hFI : IntervalIntegrable F MeasureTheory.volume a b :=
    hF.intervalIntegrable a b
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
    (entryCLM i j) hFI
  exact hcomm.symm

/-- Any single entry is dominated by the Frobenius norm. -/
theorem abs_entry_le_sqrt_frobSq (M : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : |M i j| ≤ Real.sqrt (frobSq M) := by
  have h1 : (M i j) ^ 2 ≤ frobSq M := by
    unfold frobSq
    have h2 : (M i j) ^ 2 ≤ ∑ k, (M i k) ^ 2 :=
      Finset.single_le_sum (f := fun k : Fin N => (M i k) ^ 2)
        (fun k _ => sq_nonneg (M i k)) (Finset.mem_univ j)
    refine le_trans h2 ?_
    exact Finset.single_le_sum (f := fun r : Fin N => ∑ k, (M r k) ^ 2)
      (fun r _ => Finset.sum_nonneg (fun k _ => sq_nonneg (M r k)))
      (Finset.mem_univ i)
  calc |M i j| = Real.sqrt ((M i j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (frobSq M) := Real.sqrt_le_sqrt h1

/-- The inner sandwich integrand. -/
noncomputable def innerSandwich (qs : Finset ℕ) (L u : ℝ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
    * (-(galerkinV (N := N) 1 qs ppWeightReal L))
    * NormedSpace.exp (s • (-(galerkinK (N := N) L
        + galerkinV (N := N) 1 qs ppWeightReal L)))

/-- frobSq of the inner integrand ≤ N²·frobSq(V) on the simplex. -/
theorem frobSq_innerSandwich_le (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    frobSq (innerSandwich (N := N) qs L u s)
      ≤ (N : ℝ) * frobSq (galerkinV (N := N) 1 qs ppWeightReal L) * (N : ℝ) := by
  unfold innerSandwich
  have hE1 : frobSq (NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L))))
      ≤ (N : ℝ) := by
    rw [galerkinFreeHeat_eq_diagonal]
    exact frobSq_heat_diagonal_le L (u - s) (by linarith)
  have hEKV := frobSq_exp_neg_KV_le (N := N) qs L hL s hs
  have hV0 : (0:ℝ) ≤ frobSq (galerkinV (N := N) 1 qs ppWeightReal L) :=
    frobSq_nonneg _
  calc frobSq (NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * NormedSpace.exp (s • (-(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L))))
      ≤ frobSq (NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) 1 qs ppWeightReal L)))
        * frobSq (NormedSpace.exp (s • (-(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L)))) := frobSq_mul_le _ _
    _ ≤ (frobSq (NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L))))
          * frobSq (-(galerkinV (N := N) 1 qs ppWeightReal L)))
        * frobSq (NormedSpace.exp (s • (-(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L)))) := by
        apply mul_le_mul_of_nonneg_right (frobSq_mul_le _ _) (frobSq_nonneg _)
    _ ≤ ((N : ℝ) * frobSq (galerkinV (N := N) 1 qs ppWeightReal L)) * (N : ℝ) := by
        rw [frobSq_neg]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hE1 hV0
        · exact hEKV
        · exact frobSq_nonneg _
        · positivity

#print axioms integral_entry
#print axioms abs_entry_le_sqrt_frobSq
#print axioms frobSq_innerSandwich_le

end

end RHFormalization
