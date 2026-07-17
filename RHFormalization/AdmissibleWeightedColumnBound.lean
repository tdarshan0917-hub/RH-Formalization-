import RHFormalization.AdmissibleResolventNormBound

/-!
# RHFormalization.AdmissibleWeightedColumnBound

**Front F-adm, brick 4b-ii.** The resolvent-weighted column bound (GPT-agreed
canonical form; no positivity assumptions at complex `s`):

  `‖Tr(R_D V R_H V R_D)‖ ≤ δ⁻¹ · Σₘ ‖dₘ‖²·‖V eₘ‖²`,  `dₘ = (s+μₘ)⁻¹`,

via the banked trace-cycle `= Tr(V R_H V R_D²)`, standard-basis expansion,
right absorption of `R_D²`, one Hermitian move of `V`, Cauchy–Schwarz, and
the 4b-i resolvent norm bound. The quadratic-anchor estimate on
`Σₘ‖dₘ‖²‖V eₘ‖²` is brick 4b-iii.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- Trace on the standard basis: `Tr A = Σₘ ⟪eₘ, A eₘ⟫`. -/
theorem trace_eq_sum_inner_std (A : EuclideanSpace ℂ (Fin N) →ₗ[ℂ]
    EuclideanSpace ℂ (Fin N)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) A
      = ∑ m, inner ℂ (stdBasisE N m) (A (stdBasisE N m)) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (stdBasisE N)]
  first
    | rw [Matrix.trace]
    | rfl
  refine Finset.sum_congr rfl (fun m _ => ?_)
  first
    | (rw [Matrix.diag, LinearMap.toMatrix_apply]
       unfold stdBasisE
       rw [OrthonormalBasis.coe_toBasis_repr_apply,
         OrthonormalBasis.repr_apply_apply]
       rfl)
    | (rw [Matrix.diag, LinearMap.toMatrix_apply]
       unfold stdBasisE
       simp [OrthonormalBasis.coe_toBasis_repr_apply,
         OrthonormalBasis.repr_apply_apply])
    | (simp [Matrix.diag, LinearMap.toMatrix_apply, stdBasisE,
        OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply])

/-- Hermitian `V` moves across the inner product. -/
theorem Vop_inner_move {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (u w : EuclideanSpace ℂ (Fin N)) :
    inner ℂ u (Matrix.toEuclideanLin V w)
      = inner ℂ (Matrix.toEuclideanLin V u) w := by
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin V)
      = Matrix.toEuclideanLin V := by
    first
      | (rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hV.eq])
      | (rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint.symm, hV.eq])
      | (conv_lhs => rw [← hV.eq]
         exact (Matrix.toEuclideanLin_conjTranspose_eq_adjoint V).symm)
  calc inner ℂ u (Matrix.toEuclideanLin V w)
      = inner ℂ u (LinearMap.adjoint (Matrix.toEuclideanLin V) w) := by
        rw [hadj]
    _ = inner ℂ (Matrix.toEuclideanLin V u) w := by
        first
          | exact LinearMap.adjoint_inner_right _ u w
          | rw [LinearMap.adjoint_inner_right]
          | simp [LinearMap.adjoint_inner_right]

/-- `R_D²` acts on the standard basis by `dₘ²`. -/
theorem RD_sq_apply_std (μ : Fin N → ℝ) (s : ℂ) (m : Fin N) :
    (freeResolventOpE μ s * freeResolventOpE μ s) (stdBasisE N m)
      = ((s + ((μ m : ℝ) : ℂ))⁻¹ * (s + ((μ m : ℝ) : ℂ))⁻¹)
          • stdBasisE N m := by
  have h1 : freeResolventOpE μ s (stdBasisE N m)
      = (s + ((μ m : ℝ) : ℂ))⁻¹ • stdBasisE N m := by
    unfold freeResolventOpE
    exact Basis.constr_basis _ _ _ _
  have h2 : (freeResolventOpE μ s * freeResolventOpE μ s) (stdBasisE N m)
      = freeResolventOpE μ s (freeResolventOpE μ s (stdBasisE N m)) := by
    first
      | rfl
      | rw [Module.End.mul_apply]
      | rw [LinearMap.mul_eq_comp, LinearMap.comp_apply]
  rw [h2, h1, map_smul, h1, smul_smul]

/-- **BRICK 4b-ii: the weighted-column trace bound.** -/
theorem trace_RD_V_RH_V_RD_norm_le_weighted_columns
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (s : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hlowP : ∀ i, δ ≤ ‖s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)‖) :
    ‖LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * Matrix.toEuclideanLin V
          * perturbedResolventOp μ hV s * Matrix.toEuclideanLin V
          * freeResolventOpE μ s)‖
      ≤ δ⁻¹ * ∑ m, ‖(s + ((μ m : ℝ) : ℂ))⁻¹‖ ^ 2
          * ‖Matrix.toEuclideanLin V (stdBasisE N m)‖ ^ 2 := by
  rw [residual_trace_cycle μ hV s, trace_eq_sum_inner_std]
  set RD := freeResolventOpE μ s
  set RH := perturbedResolventOp μ hV s
  set Vop := Matrix.toEuclideanLin V
  have hterm : ∀ m : Fin N,
      ‖inner ℂ (stdBasisE N m) ((Vop * RH * Vop * (RD * RD)) (stdBasisE N m))‖
        ≤ δ⁻¹ * (‖(s + ((μ m : ℝ) : ℂ))⁻¹‖ ^ 2 * ‖Vop (stdBasisE N m)‖ ^ 2) := by
    intro m
    set d : ℂ := (s + ((μ m : ℝ) : ℂ))⁻¹ with hd
    have hRDsq : (RD * RD) (stdBasisE N m) = (d * d) • stdBasisE N m :=
      RD_sq_apply_std μ s m
    have happ : (Vop * RH * Vop * (RD * RD)) (stdBasisE N m)
        = (d * d) • (Vop (RH (Vop (stdBasisE N m)))) := by
      have hcomp : (Vop * RH * Vop * (RD * RD)) (stdBasisE N m)
          = Vop (RH (Vop ((RD * RD) (stdBasisE N m)))) := by
        first
          | rfl
          | simp [Module.End.mul_apply]
          | simp [LinearMap.mul_eq_comp, LinearMap.comp_apply]
      rw [hcomp, hRDsq, map_smul, map_smul, map_smul]
    rw [happ, inner_smul_right, norm_mul]
    have hmove : inner ℂ (stdBasisE N m) (Vop (RH (Vop (stdBasisE N m))))
        = inner ℂ (Vop (stdBasisE N m)) (RH (Vop (stdBasisE N m))) :=
      Vop_inner_move hV _ _
    rw [hmove]
    have hCS : ‖inner ℂ (Vop (stdBasisE N m)) (RH (Vop (stdBasisE N m)))‖
        ≤ ‖Vop (stdBasisE N m)‖ * ‖RH (Vop (stdBasisE N m))‖ :=
      norm_inner_le_norm _ _
    have hRH : ‖RH (Vop (stdBasisE N m))‖
        ≤ δ⁻¹ * ‖Vop (stdBasisE N m)‖ :=
      perturbedResolventOp_norm_le μ hV s hδ hlowP _
    have hdd : ‖d * d‖ = ‖d‖ ^ 2 := by rw [norm_mul, sq]
    rw [hdd]
    have h1 : ‖inner ℂ (Vop (stdBasisE N m)) (RH (Vop (stdBasisE N m)))‖
        ≤ ‖Vop (stdBasisE N m)‖ * (δ⁻¹ * ‖Vop (stdBasisE N m)‖) :=
      le_trans hCS (mul_le_mul_of_nonneg_left hRH (norm_nonneg _))
    have h2 : (0:ℝ) ≤ ‖d‖ ^ 2 := sq_nonneg _
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    refine le_trans h3 (le_of_eq ?_)
    ring
  calc ‖∑ m, inner ℂ (stdBasisE N m)
        ((Vop * RH * Vop * (RD * RD)) (stdBasisE N m))‖
      ≤ ∑ m, ‖inner ℂ (stdBasisE N m)
          ((Vop * RH * Vop * (RD * RD)) (stdBasisE N m))‖ := norm_sum_le _ _
    _ ≤ ∑ m, δ⁻¹ * (‖(s + ((μ m : ℝ) : ℂ))⁻¹‖ ^ 2
          * ‖Vop (stdBasisE N m)‖ ^ 2) :=
        Finset.sum_le_sum (fun m _ => hterm m)
    _ = δ⁻¹ * ∑ m, ‖(s + ((μ m : ℝ) : ℂ))⁻¹‖ ^ 2
          * ‖Vop (stdBasisE N m)‖ ^ 2 := by rw [Finset.mul_sum]

#print axioms trace_eq_sum_inner_std
#print axioms Vop_inner_move
#print axioms RD_sq_apply_std
#print axioms trace_RD_V_RH_V_RD_norm_le_weighted_columns

end

end RHFormalization
