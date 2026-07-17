import RHFormalization.AdmissibleFirstOrderDiagonal

/-!
# RHFormalization.AdmissibleResolventNormBound

**Front F-adm, brick 4b-i.** The perturbed resolvent operator-norm bound:

  `‖R_H x‖ ≤ δ⁻¹ · ‖x‖`  whenever `δ ≤ ‖s + λᵢ‖` for all `i`,

via the eigen-coordinate formula (R_H multiplies eigenbasis coordinates by
`(s+λᵢ)⁻¹`) and Parseval. Pure norm estimates — no positivity at complex `s`.
Foundation of the weighted-column residual bound (4b-ii).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- The eigenbasis as an OrthonormalBasis (abbreviation). -/
def pONB (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ}
    (hV : V.IsHermitian) : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  (perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank

/-- The resolvent acts diagonally on the orthonormal eigenbasis. -/
theorem perturbedResolventOp_apply_ONB (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ) (j : Fin N) :
    perturbedResolventOp μ hV s (pONB μ hV j)
      = (s + ((perturbedEigenvalues μ hV j : ℝ) : ℂ))⁻¹ • pONB μ hV j := by
  have hbe : perturbedEigenBasis μ hV j = pONB μ hV j := by
    unfold perturbedEigenBasis pONB
    first
      | rw [OrthonormalBasis.coe_toBasis]
      | simp [OrthonormalBasis.coe_toBasis]
      | rfl
  rw [← hbe]
  unfold perturbedResolventOp
  rw [Basis.constr_basis]
  all_goals rw [hbe]

/-- **Eigen-coordinate formula**: `(R_H x)ᵢ = (s+λᵢ)⁻¹ · xᵢ` in eigenbasis
coordinates. -/
theorem perturbedResolventOp_repr (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (pONB μ hV).repr (perturbedResolventOp μ hV s x) i
      = (s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹
          * (pONB μ hV).repr x i := by
  classical
  set b := pONB μ hV with hb
  have hact : ∀ j : Fin N,
      perturbedResolventOp μ hV s (b j)
        = (s + ((perturbedEigenvalues μ hV j : ℝ) : ℂ))⁻¹ • b j := by
    intro j
    rw [hb]
    exact perturbedResolventOp_apply_ONB μ hV s j
  have hON := orthonormal_iff_ite.mp b.orthonormal
  have hvec : perturbedResolventOp μ hV s x
      = ∑ j, ((s + ((perturbedEigenvalues μ hV j : ℝ) : ℂ))⁻¹
          * b.repr x j) • b j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    first
      | (rw [map_smul, hact j, smul_smul, mul_comm])
      | (rw [map_smul, hact j, smul_smul]; congr 1; ring)
  have hinner : ∀ y : EuclideanSpace ℂ (Fin N),
      b.repr y i = inner ℂ (b i) y := fun y => b.repr_apply_apply y i
  conv_lhs => rw [hinner (perturbedResolventOp μ hV s x)]
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

/-- **BRICK 4b-i: the resolvent operator-norm bound** `‖R_H x‖ ≤ δ⁻¹‖x‖`. -/
theorem perturbedResolventOp_norm_le (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ i, δ ≤ ‖s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)‖)
    (x : EuclideanSpace ℂ (Fin N)) :
    ‖perturbedResolventOp μ hV s x‖ ≤ δ⁻¹ * ‖x‖ := by
  set b := pONB μ hV with hb
  have hnx : ‖x‖ = ‖b.repr x‖ := (b.repr.norm_map x).symm
  have hnR : ‖perturbedResolventOp μ hV s x‖
      = ‖b.repr (perturbedResolventOp μ hV s x)‖ :=
    (b.repr.norm_map _).symm
  rw [hnx, hnR]
  have hsq1 : ‖b.repr (perturbedResolventOp μ hV s x)‖
      = Real.sqrt (∑ i, ‖b.repr (perturbedResolventOp μ hV s x) i‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq _
      | exact PiLp.norm_eq_of_L2 _ _
  have hsq2 : ‖b.repr x‖ = Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq _
      | exact PiLp.norm_eq_of_L2 _ _
  rw [hsq1, hsq2]
  have hterm : ∀ i : Fin N,
      ‖b.repr (perturbedResolventOp μ hV s x) i‖ ^ 2
        ≤ δ⁻¹ ^ 2 * ‖b.repr x i‖ ^ 2 := by
    intro i
    rw [hb, perturbedResolventOp_repr μ hV s x i, ← hb, norm_mul, mul_pow]
    have h1 : ‖(s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹‖ ≤ δ⁻¹ := by
      rw [norm_inv]
      have hpos : (0:ℝ) < ‖s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)‖ :=
        lt_of_lt_of_le hδ (hlow i)
      first
        | exact inv_le_inv_of_le hδ (hlow i)
        | exact (inv_le_inv₀ hpos hδ).mpr (hlow i)
        | (apply inv_le_inv_of_le hδ (hlow i))
    have h2 : (0:ℝ) ≤ ‖(s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹‖ :=
      norm_nonneg _
    have h3 : (0:ℝ) ≤ ‖b.repr x i‖ ^ 2 := sq_nonneg _
    have h4 : ‖(s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹‖ ^ 2
        ≤ δ⁻¹ ^ 2 := by nlinarith [h1, h2]
    exact mul_le_mul_of_nonneg_right h4 h3
  have hsum : (∑ i, ‖b.repr (perturbedResolventOp μ hV s x) i‖ ^ 2)
      ≤ δ⁻¹ ^ 2 * ∑ i, ‖b.repr x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  calc Real.sqrt (∑ i, ‖b.repr (perturbedResolventOp μ hV s x) i‖ ^ 2)
      ≤ Real.sqrt (δ⁻¹ ^ 2 * ∑ i, ‖b.repr x i‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = δ⁻¹ * Real.sqrt (∑ i, ‖b.repr x i‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _)]
        congr 1
        first
          | exact Real.sqrt_sq (by positivity)
          | rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ δ⁻¹)]

#print axioms perturbedResolventOp_apply_ONB
#print axioms perturbedResolventOp_repr
#print axioms perturbedResolventOp_norm_le

end

end RHFormalization
