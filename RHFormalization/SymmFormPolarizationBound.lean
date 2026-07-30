-- SENTINEL: symm-form-polarization-bound-v2
import RHFormalization.GalerkinFormBound
import RHFormalization.AdmissibleEigenvalueFloor
import Mathlib

/-!
# Polarization: form bound ⟹ ℓ² operator bound (sum-of-squares form)
Generic: symmetric `M` with `|form_M(v)| ≤ C·Σv²` satisfies
`Σ((M.mulVec a)ᵢ)² ≤ C²·Σaᵢ²`. v2: bilinearity-lemma expansion (no
sum_sub_distrib), division-free squeeze via test vector `C·a`.
DOWNSTREAM CONSUMER: |(V·E₁·V·E₂)ₘₘ| ≤ SupVConst² route → h_conv.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Bilinear pairing through the matrix. -/
def formBilin (M : Matrix (Fin N) (Fin N) ℝ) (u v : Fin N → ℝ) : ℝ :=
  ∑ m : Fin N, ∑ n : Fin N, u m * v n * M m n

theorem formBilin_eq_sum_mulVec (M : Matrix (Fin N) (Fin N) ℝ)
    (u v : Fin N → ℝ) :
    formBilin M u v = ∑ i : Fin N, u i * (M.mulVec v) i := by
  unfold formBilin
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have happ : (M.mulVec v) m = ∑ n : Fin N, M m n * v n := by
    first
      | simp [Matrix.mulVec, Matrix.dotProduct]
      | simp [Matrix.mulVec, dotProduct]
  rw [happ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem formBilin_add_left (M : Matrix (Fin N) (Fin N) ℝ)
    (u w v : Fin N → ℝ) :
    formBilin M (fun i => u i + w i) v
      = formBilin M u v + formBilin M w v := by
  unfold formBilin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem formBilin_add_right (M : Matrix (Fin N) (Fin N) ℝ)
    (u v w : Fin N → ℝ) :
    formBilin M u (fun i => v i + w i)
      = formBilin M u v + formBilin M u w := by
  unfold formBilin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem formBilin_smul_left (M : Matrix (Fin N) (Fin N) ℝ)
    (u v : Fin N → ℝ) (t : ℝ) :
    formBilin M (fun i => t * u i) v = t * formBilin M u v := by
  unfold formBilin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem formBilin_smul_right (M : Matrix (Fin N) (Fin N) ℝ)
    (u v : Fin N → ℝ) (t : ℝ) :
    formBilin M u (fun i => t * v i) = t * formBilin M u v := by
  unfold formBilin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

theorem formBilin_symm (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.IsSymm)
    (u v : Fin N → ℝ) :
    formBilin M u v = formBilin M v u := by
  unfold formBilin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hMnm : M n m = M m n := by
    conv_lhs => rw [← hM.eq]
    rw [Matrix.transpose_apply]
  rw [hMnm]
  ring

/-- Polarization: quadratic-form bound ⟹ bilinear bound. -/
theorem abs_formBilin_le (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.IsSymm)
    (C : ℝ)
    (hform : ∀ v : Fin N → ℝ,
      |formBilin M v v| ≤ C * ∑ i : Fin N, (v i) ^ 2)
    (u v : Fin N → ℝ) :
    |formBilin M u v|
      ≤ (C / 2) * ((∑ i : Fin N, (u i) ^ 2) + ∑ i : Fin N, (v i) ^ 2) := by
  have hplus := hform (fun i => u i + v i)
  have hminus := hform (fun i => u i - v i)
  have hsymm := formBilin_symm M hM v u
  have hQplus : formBilin M (fun i => u i + v i) (fun i => u i + v i)
      = formBilin M u u + formBilin M v v + 2 * formBilin M u v := by
    rw [formBilin_add_left, formBilin_add_right, formBilin_add_right, hsymm]
    ring
  have hmv : (fun i => u i - v i) = (fun i => u i + (-1 : ℝ) * v i) := by
    funext i
    ring
  have hQminus : formBilin M (fun i => u i - v i) (fun i => u i - v i)
      = formBilin M u u + formBilin M v v - 2 * formBilin M u v := by
    rw [hmv, formBilin_add_left, formBilin_add_right, formBilin_add_right,
      formBilin_smul_right, formBilin_smul_left, formBilin_smul_left,
      formBilin_smul_right, hsymm]
    ring
  have hSplus : ∑ i : Fin N, (u i + v i) ^ 2
      = (∑ i : Fin N, (u i) ^ 2) + (∑ i : Fin N, (v i) ^ 2)
        + 2 * ∑ i : Fin N, u i * v i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hSminus : ∑ i : Fin N, (u i - v i) ^ 2
      = ((∑ i : Fin N, (u i) ^ 2) + (∑ i : Fin N, (v i) ^ 2))
        + (-2) * ∑ i : Fin N, u i * v i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hQplus, hSplus] at hplus
  rw [hQminus, hSminus] at hminus
  have habs1 := abs_le.mp hplus
  have habs2 := abs_le.mp hminus
  rw [abs_le]
  constructor <;> nlinarith [habs1.1, habs1.2, habs2.1, habs2.2]

/-- **POLARIZATION CAPSTONE.** Symmetric form bound ⟹ ℓ²-mulVec bound.
Division-free: test vector `C·a`. -/
theorem symmFormBound_mulVec_sumSq_le
    (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.IsSymm) (C : ℝ) (hC : 0 ≤ C)
    (hform : ∀ v : Fin N → ℝ,
      |formBilin M v v| ≤ C * ∑ i : Fin N, (v i) ^ 2)
    (a : Fin N → ℝ) :
    ∑ i : Fin N, ((M.mulVec a) i) ^ 2 ≤ C ^ 2 * ∑ i : Fin N, (a i) ^ 2 := by
  set P : ℝ := ∑ i : Fin N, ((M.mulVec a) i) ^ 2 with hP
  set Sa : ℝ := ∑ i : Fin N, (a i) ^ 2 with hSa
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  have hSann : 0 ≤ Sa := by rw [hSa]; positivity
  have hBP : formBilin M (M.mulVec a) a = P := by
    rw [formBilin_eq_sum_mulVec, hP]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  by_cases hC0 : C = 0
  · have hbase := abs_formBilin_le M hM C hform (M.mulVec a) a
    rw [hBP, abs_of_nonneg hPnn, hC0] at hbase
    have hz : (0:ℝ) / 2 * ((∑ i : Fin N, ((M.mulVec a) i) ^ 2) + Sa) = 0 := by
      ring
    rw [hz] at hbase
    rw [hC0]
    nlinarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hb := abs_formBilin_le M hM C hform (M.mulVec a)
      (fun i => C * a i)
    rw [formBilin_smul_right, hBP] at hb
    have hSca : ∑ i : Fin N, ((fun i => C * a i) i) ^ 2 = C ^ 2 * Sa := by
      rw [hSa, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hSca] at hb
    rw [abs_of_nonneg (mul_nonneg hC hPnn)] at hb
    -- hb : C * P ≤ C / 2 * ((∑ (Ma i)²) + C² * Sa); first summand is P (set-folded)
    by_contra hgoal
    push_neg at hgoal
    have hexp : C / 2 * (P + C ^ 2 * Sa)
        = C / 2 * P + C / 2 * (C ^ 2 * Sa) := by
      ring
    rw [hexp] at hb
    have hkey : C / 2 * (C ^ 2 * Sa) < C / 2 * P :=
      mul_lt_mul_of_pos_left hgoal (by positivity)
    have hcontra : C * P < C * P := by
      calc C * P ≤ C / 2 * P + C / 2 * (C ^ 2 * Sa) := hb
        _ < C / 2 * P + C / 2 * P := by linarith
        _ = C * P := by ring
    exact lt_irrefl _ hcontra

/-- **Stage discharge (L = 1):** the genuine bump matrix is an ℓ²-bounded
operator with constant SupVConst, uniformly in N and qs. -/
theorem galerkinV_mulVec_sumSq_le (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ i : Fin N,
      (((galerkinV (N := N) 1 qs ppWeightReal 1).mulVec a) i) ^ 2
      ≤ SupVConst ^ 2 * ∑ i : Fin N, (a i) ^ 2 := by
  refine symmFormBound_mulVec_sumSq_le _ (galerkinV_symm 1 qs ppWeightReal 1)
    SupVConst ?_ ?_ a
  · first
      | exact SupVConst_nonneg_adm
      | exact SupVConst_nonneg
      | positivity
  · intro v
    have h := galerkinV_form_bound (N := N) qs v
    unfold formBilin
    exact h

#print axioms formBilin_eq_sum_mulVec
#print axioms formBilin_add_left
#print axioms formBilin_add_right
#print axioms formBilin_smul_left
#print axioms formBilin_smul_right
#print axioms formBilin_symm
#print axioms abs_formBilin_le
#print axioms symmFormBound_mulVec_sumSq_le
#print axioms galerkinV_mulVec_sumSq_le
