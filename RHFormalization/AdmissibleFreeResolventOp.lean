import RHFormalization.AdmissibleResolventBridge

/-!
# RHFormalization.AdmissibleFreeResolventOp

**Front F-adm, brick 3b-i.** The free twin of the 3a bridge, on the STANDARD
basis (keeps the original `μ`-indexing, so the trace matches 2b-i's
`FstageFinite μ` directly — no sorted-spectrum mismatch), plus the generic
finite-dimensional right⟹left inverse flip. Feeds the exact second-resolvent
identity (3b-ii).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- The standard (orthonormal) basis of `EuclideanSpace ℂ (Fin N)` as a basis. -/
def stdBasisE (N : ℕ) : Basis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  (EuclideanSpace.basisFun (Fin N) ℂ).toBasis

/-- The free diagonal operator on Euclidean space. -/
def freeOpE (μ : Fin N → ℝ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanLin (freeDiag μ)

/-- The free operator acts diagonally on the standard basis. -/
theorem freeOpE_apply_stdBasis (μ : Fin N → ℝ) (i : Fin N) :
    freeOpE μ (stdBasisE N i) = ((μ i : ℝ) : ℂ) • stdBasisE N i := by
  unfold freeOpE stdBasisE freeDiag
  apply (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.repr.injective
  ext j
  first
    | (simp [Matrix.toEuclideanLin, Matrix.mulVec_diagonal,
        EuclideanSpace.basisFun, Pi.single_apply, mul_comm, mul_ite]
       by_cases h : j = i <;> simp [h, Pi.single_apply])
    | (simp [Matrix.toEuclideanLin, Matrix.mulVec_diagonal,
        Pi.single_apply, mul_comm]
       by_cases h : j = i <;> simp [h])
    | (simp [Matrix.toEuclideanLin_eq_toLin, Matrix.toLin'_apply,
        Matrix.mulVec_diagonal, Pi.single_apply, mul_comm]
       by_cases h : j = i <;> simp [h])

/-- **The free constructed resolvent** on the standard basis:
`R_D(e_i) = (s + μ_i)⁻¹ • e_i`. -/
def freeResolventOpE (μ : Fin N → ℝ) (s : ℂ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (stdBasisE N).constr ℂ
    (fun i => (s + ((μ i : ℝ) : ℂ))⁻¹ • stdBasisE N i)

/-- **Free spectral bridge**: the trace of the free resolvent IS
`FstageFinite μ` — with the ORIGINAL indexing. -/
theorem freeResolventOpE_trace (μ : Fin N → ℝ) (s : ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (freeResolventOpE μ s)
      = FstageFinite μ s := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (stdBasisE N)]
  unfold FstageFinite
  first
    | rw [Matrix.trace]
    | rfl
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | (rw [Matrix.diag, LinearMap.toMatrix_apply]
       unfold freeResolventOpE
       rw [Basis.constr_basis, map_smul, Basis.repr_self]
       simp)
    | (simp [Matrix.diag, LinearMap.toMatrix_apply, freeResolventOpE,
        Basis.constr_basis, Basis.repr_self])

/-- The free constructed resolvent is a right inverse of `s•1 + D`. -/
theorem freeResolvent_right_inverse (μ : Fin N → ℝ) (s : ℂ)
    (hne : ∀ i, s + ((μ i : ℝ) : ℂ) ≠ 0) :
    (s • LinearMap.id + freeOpE μ) ∘ₗ freeResolventOpE μ s
      = LinearMap.id := by
  apply (stdBasisE N).ext
  intro i
  rw [LinearMap.comp_apply]
  have h1 : freeResolventOpE μ s (stdBasisE N i)
      = (s + ((μ i : ℝ) : ℂ))⁻¹ • stdBasisE N i := by
    unfold freeResolventOpE
    exact Basis.constr_basis _ _ _ _
  rw [h1, map_smul]
  set T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    s • LinearMap.id + freeOpE μ with hT
  have h2 : T (stdBasisE N i)
      = (s + ((μ i : ℝ) : ℂ)) • stdBasisE N i := by
    rw [hT, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      freeOpE_apply_stdBasis μ i, ← add_smul]
  rw [h2, smul_smul, inv_mul_cancel₀ (hne i), one_smul, LinearMap.id_apply]

/-- **Generic finite-dimensional inverse flip**: a right inverse is a left
inverse. -/
theorem comp_eq_id_comm
    (f g : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (h : f ∘ₗ g = LinearMap.id) : g ∘ₗ f = LinearMap.id := by
  have hmul : f * g = 1 := by
    first
      | exact h
      | (show f ∘ₗ g = LinearMap.id; exact h)
      | (rw [LinearMap.mul_eq_comp, LinearMap.one_eq_id]; exact h)
  have hflip : g * f = 1 := by
    first
      | exact (LinearMap.mul_eq_one_comm).mp hmul
      | exact (Module.End.mul_eq_one_comm).mp hmul
      | exact mul_eq_one_comm.mp hmul
  first
    | exact hflip
    | (rw [← LinearMap.mul_eq_comp, ← LinearMap.one_eq_id]; exact hflip)

/-- Left-inverse form for the perturbed resolvent. -/
theorem resolvent_left_inverse (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (hne : ∀ i, s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0) :
    perturbedResolventOp μ hV s ∘ₗ (s • LinearMap.id + perturbedOp μ V)
      = LinearMap.id :=
  comp_eq_id_comm _ _ (resolvent_right_inverse μ hV s hne)

/-- Left-inverse form for the free resolvent. -/
theorem freeResolvent_left_inverse (μ : Fin N → ℝ) (s : ℂ)
    (hne : ∀ i, s + ((μ i : ℝ) : ℂ) ≠ 0) :
    freeResolventOpE μ s ∘ₗ (s • LinearMap.id + freeOpE μ)
      = LinearMap.id :=
  comp_eq_id_comm _ _ (freeResolvent_right_inverse μ s hne)

#print axioms freeOpE_apply_stdBasis
#print axioms freeResolventOpE_trace
#print axioms freeResolvent_right_inverse
#print axioms comp_eq_id_comm
#print axioms resolvent_left_inverse
#print axioms freeResolvent_left_inverse

end

end RHFormalization
