import RHFormalization.PrimePotentialDecodedCenter
import RHFormalization.DecodedEigenvalueFloor
import RHFormalization.DecodedVEntryBound
import RHFormalization.DenseGalerkinSchedule
import RHFormalization.DenseSharpMassSchedule
import RHFormalization.DenseStageBoundUniform
import RHFormalization.AdmissibleS1MassBound
import Mathlib

/-!
B(i)-4 (part 1, decoded substitution): the dense-stage prime potential
built on the DECODED-center Galerkin matrix (bumps at `(ppDecode k).center`
= log p^m, manuscript-faithful — the banked `galerkinV` carries the
log-of-code trap and is NOT used here).

1. `denseV n` := decodedGalerkinV at (δ=1, codes below admR n, ppWeightReal,
   denseL n), dimension denseN n.
2. PSD form + diagonal nonneg (instantiating banked
   `decodedGalerkinV_form_nonneg_L`).
3. Entry bound |V_kj| ≤ (2/denseL)·S1mass(admR) ≤ 24(log4+4)·(n+2)^{-1/8}
   — in X-variables this is 24(log4+4)·X^{-1/4} (X = √(n+2)), the frozen
   B(i)-4 rate.
denseQV deferred to the GPT shape ruling (separate file).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Dense-stage decoded-center potential matrix. -/
noncomputable def denseV (n : ℕ) :
    Matrix (Fin (denseN n)) (Fin (denseN n)) ℝ :=
  decodedGalerkinV (N := denseN n) 1
    (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (denseL n)

/-- The dense decoded bump form is nonnegative. -/
theorem denseV_form_nonneg (n : ℕ) (a : Fin (denseN n) → ℝ) :
    0 ≤ ∑ m : Fin (denseN n), ∑ j : Fin (denseN n),
        a m * a j * denseV n m j := by
  have hL0 : (0:ℝ) < denseL n :=
    lt_of_lt_of_le (by norm_num) (eight_le_denseL n)
  unfold denseV
  exact decodedGalerkinV_form_nonneg_L (denseL n) hL0 _ a

/-- Diagonal entries are nonnegative (basis-vector plug-in). -/
theorem denseV_diag_nonneg (n : ℕ) (k : Fin (denseN n)) :
    0 ≤ denseV n k k := by
  have h := denseV_form_nonneg n (fun i => if i = k then (1:ℝ) else 0)
  have hred : ∑ m : Fin (denseN n), ∑ j : Fin (denseN n),
      (if m = k then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)
        * denseV n m j
      = denseV n k k := by
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro j _
      simp [hb]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hred] at h
  exact h

/-- **Entry bound, mass form**: `|denseV_{kj}| ≤ (2/denseL)·S1mass(admR)`. -/
theorem abs_denseV_entry_le (n : ℕ) (k j : Fin (denseN n)) :
    |denseV n k j| ≤ (2 / denseL n) * S1mass (admR n) := by
  have hL0 : (0:ℝ) < denseL n :=
    lt_of_lt_of_le (by norm_num) (eight_le_denseL n)
  have h2L : (0:ℝ) ≤ 2 / denseL n := le_of_lt (div_pos (by norm_num) hL0)
  unfold denseV decodedGalerkinV
  rw [abs_mul, abs_of_nonneg h2L]
  refine mul_le_mul_of_nonneg_left ?_ h2L
  calc |decodedVmatrixElement 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (denseL n) ((k : ℕ) + 1) ((j : ℕ) + 1)|
      ≤ ∑ q ∈ activePrimePowerCodesCenterBelow (admR n), |ppWeightReal q| :=
        abs_decodedVmatrixElement_le _ ppWeightReal (denseL n) hL0.le _ _
    _ = S1mass (admR n) := by
        unfold S1mass
        exact Finset.sum_congr rfl
          (fun q _ => abs_of_nonneg (ppWeightReal_nonneg q))

/-- **Entry bound, schedule form (frozen B(i)-4 rate)**:
`|denseV_{kj}| ≤ 24(log4+4)·(n+2)^{-1/8} = 24(log4+4)·X^{-1/4}`. -/
theorem abs_denseV_entry_le_rpow (n : ℕ) (k j : Fin (denseN n)) :
    |denseV n k j|
      ≤ 24 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ (-(1:ℝ)/8) := by
  have hn2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have hL0 : (0:ℝ) < denseL n :=
    lt_of_lt_of_le (by norm_num) (eight_le_denseL n)
  have h2L : (0:ℝ) ≤ 2 / denseL n := le_of_lt (div_pos (by norm_num) hL0)
  have hlog : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : (0:ℝ) ≤ Real.log 4 + 4 := by linarith
  have hS : S1mass (admR n)
      ≤ 12 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ ((1:ℝ)/4) := by
    have h := S1mass_admR_le_sqrt_exp n
    rwa [sqrt_exp_admR_eq_rpow_quarter] at h
  have hinv : (denseL n)⁻¹ ≤ (((n : ℝ) + 2) ^ ((3:ℝ)/8))⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hn2 _) (rpow_le_denseL n)
  have hfrac : 2 / denseL n ≤ 2 * (((n : ℝ) + 2) ^ ((3:ℝ)/8))⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hx4 : (0:ℝ) ≤ ((n : ℝ) + 2) ^ ((1:ℝ)/4) :=
    Real.rpow_nonneg hn2.le _
  have hRHSnn : (0:ℝ)
      ≤ 12 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ ((1:ℝ)/4) :=
    mul_nonneg (mul_nonneg (by norm_num) hB) hx4
  calc |denseV n k j|
      ≤ (2 / denseL n) * S1mass (admR n) := abs_denseV_entry_le n k j
    _ ≤ (2 / denseL n)
          * (12 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ ((1:ℝ)/4)) :=
        mul_le_mul_of_nonneg_left hS h2L
    _ ≤ (2 * (((n : ℝ) + 2) ^ ((3:ℝ)/8))⁻¹)
          * (12 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ ((1:ℝ)/4)) :=
        mul_le_mul_of_nonneg_right hfrac hRHSnn
    _ = 24 * (Real.log 4 + 4)
          * (((n : ℝ) + 2) ^ ((1:ℝ)/4) * (((n : ℝ) + 2) ^ ((3:ℝ)/8))⁻¹) := by
        ring
    _ = 24 * (Real.log 4 + 4) * ((n : ℝ) + 2) ^ (-(1:ℝ)/8) := by
        congr 1
        rw [← Real.rpow_neg hn2.le, ← Real.rpow_add hn2]
        first
          | norm_num
          | (congr 1; norm_num)
          | (congr 1; ring)

#print axioms denseV_form_nonneg
#print axioms denseV_diag_nonneg
#print axioms abs_denseV_entry_le
#print axioms abs_denseV_entry_le_rpow

end

end RHFormalization
