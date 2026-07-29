-- SENTINEL: FREERESNORM-v2
import RHFormalization.AdmissibleResolventNormBound
import RHFormalization.AdmissibleFreeResolventOp
import Mathlib

/-!
# FreeResolventNormBound — the free twin of banked brick 4b-i

CONSUMER: the operator-factor estimate in the ‖Z‖ remainder bound
(‖Z‖ feeds `hr` of `seam_bdd_of_parts` → `h_ctail_le_of_seam_bdd` → GATE).

`‖R_D x‖ ≤ δ⁻¹‖x‖` when `δ ≤ ‖s + μᵢ‖` for all i. Same Parseval argument as
the banked `perturbedResolventOp_norm_le`, on the standard orthonormal basis.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- The standard orthonormal basis of Euclidean space. -/
def sONB (N : ℕ) : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  EuclideanSpace.basisFun (Fin N) ℂ

/-- The free resolvent acts diagonally on the standard orthonormal basis. -/
theorem freeResolventOpE_apply_ONB (μ : Fin N → ℝ) (s : ℂ) (j : Fin N) :
    freeResolventOpE μ s (sONB N j)
      = (s + ((μ j : ℝ) : ℂ))⁻¹ • sONB N j := by
  have hbe : stdBasisE N j = sONB N j := by
    unfold stdBasisE sONB
    first
      | rw [OrthonormalBasis.coe_toBasis]
      | simp [OrthonormalBasis.coe_toBasis]
      | rfl
  rw [← hbe]
  unfold freeResolventOpE
  rw [Basis.constr_basis]
  all_goals rw [hbe]

/-- Coordinate formula: `(R_D x)ᵢ = (s+μᵢ)⁻¹ xᵢ`. -/
theorem freeResolventOpE_repr (μ : Fin N → ℝ) (s : ℂ)
    (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (sONB N).repr (freeResolventOpE μ s x) i
      = (s + ((μ i : ℝ) : ℂ))⁻¹ * (sONB N).repr x i := by
  classical
  set b := sONB N with hb
  have hact : ∀ j : Fin N,
      freeResolventOpE μ s (b j) = (s + ((μ j : ℝ) : ℂ))⁻¹ • b j := by
    intro j
    rw [hb]
    exact freeResolventOpE_apply_ONB μ s j
  have hON := orthonormal_iff_ite.mp b.orthonormal
  have hvec : freeResolventOpE μ s x
      = ∑ j, ((s + ((μ j : ℝ) : ℂ))⁻¹ * b.repr x j) • b j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    first
      | (rw [map_smul, hact j, smul_smul, mul_comm])
      | (rw [map_smul, hact j, smul_smul]; congr 1; ring)
  have hinner : ∀ y : EuclideanSpace ℂ (Fin N),
      b.repr y i = inner ℂ (b i) y := fun y => b.repr_apply_apply y i
  conv_lhs => rw [hinner (freeResolventOpE μ s x)]
  rw [hvec, inner_sum]
  simp only [inner_smul_right]
  rw [Finset.sum_eq_single i
    (fun j _ hji => by rw [hON i j, if_neg (Ne.symm hji), mul_zero])
    (fun hni => absurd (Finset.mem_univ i) hni)]
  first
    | (rw [hON i i, if_pos rfl, mul_one])
    | (rw [hON i i]; simp)
    | (simp [hON])
    | (rw [hON i i, if_pos rfl]; ring)

/-- **The free resolvent operator-norm bound** `‖R_D x‖ ≤ δ⁻¹‖x‖`. -/
theorem freeResolventOpE_norm_le (μ : Fin N → ℝ) (s : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ i, δ ≤ ‖s + ((μ i : ℝ) : ℂ)‖)
    (x : EuclideanSpace ℂ (Fin N)) :
    ‖freeResolventOpE μ s x‖ ≤ δ⁻¹ * ‖x‖ := by
  set b := sONB N with hb
  have hnx : ‖x‖ = ‖b.repr x‖ := (b.repr.norm_map x).symm
  have hnR : ‖freeResolventOpE μ s x‖ = ‖b.repr (freeResolventOpE μ s x)‖ :=
    (b.repr.norm_map _).symm
  rw [hnx, hnR]
  have hsq1 : ‖b.repr (freeResolventOpE μ s x)‖
      = Real.sqrt (∑ i, ‖b.repr (freeResolventOpE μ s x) i‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq _
      | exact PiLp.norm_eq_of_L2 _ _
  have hsq2 : ‖b.repr x‖ = Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq _
      | exact PiLp.norm_eq_of_L2 _ _
  rw [hsq1, hsq2]
  have hterm : ∀ i : Fin N,
      ‖b.repr (freeResolventOpE μ s x) i‖ ^ 2 ≤ δ⁻¹ ^ 2 * ‖b.repr x i‖ ^ 2 := by
    intro i
    rw [hb, freeResolventOpE_repr μ s x i, ← hb, norm_mul, mul_pow]
    have h1 : ‖(s + ((μ i : ℝ) : ℂ))⁻¹‖ ≤ δ⁻¹ := by
      rw [norm_inv]
      have hpos : (0:ℝ) < ‖s + ((μ i : ℝ) : ℂ)‖ := lt_of_lt_of_le hδ (hlow i)
      first
        | exact inv_le_inv_of_le hδ (hlow i)
        | exact (inv_le_inv₀ hpos hδ).mpr (hlow i)
    have h2 : (0:ℝ) ≤ ‖(s + ((μ i : ℝ) : ℂ))⁻¹‖ := norm_nonneg _
    have hsq : ‖(s + ((μ i : ℝ) : ℂ))⁻¹‖ ^ 2 ≤ δ⁻¹ ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul h1 h1 h2 (by positivity)
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hsum : (∑ i, ‖b.repr (freeResolventOpE μ s x) i‖ ^ 2)
      ≤ δ⁻¹ ^ 2 * ∑ i, ‖b.repr x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  calc Real.sqrt (∑ i, ‖b.repr (freeResolventOpE μ s x) i‖ ^ 2)
      ≤ Real.sqrt (δ⁻¹ ^ 2 * ∑ i, ‖b.repr x i‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = δ⁻¹ * Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

#print axioms freeResolventOpE_apply_ONB
#print axioms freeResolventOpE_repr
#print axioms freeResolventOpE_norm_le

end

end RHFormalization
