import RHFormalization.AdmissiblePrimeStageIdentity

/-!
# RHFormalization.AdmissibleResolventBridge

**Front F-adm, brick 3a (Gate 1 of the 2b-ii design).** The finite Hermitian
resolvent spectral bridge, built CONSTRUCTIVELY at operator level — no
`Matrix.inv`, no diagonalization theorem:

* `perturbedResolventOp` — the resolvent DEFINED on the eigenvector basis
  (`Basis.constr`, diagonal by construction);
* `perturbedResolventOp_trace` — its trace IS `FstageFinite (perturbedEigenvalues)`;
* `resolvent_right_inverse` — `(s•1 + H) ∘ R = id` (so it deserves the name).

The pure second-resolvent algebra identity and the FirstOrderWindow /
HigherResidual split (Gate 2 layering) are brick 3b.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- The eigenvector basis of the perturbed operator, as a plain basis. -/
def perturbedEigenBasis (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ}
    (hV : V.IsHermitian) : Basis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  ((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank).toBasis

/-- **The constructed resolvent**: on the eigenvector basis,
`R (v_i) = (s + λ_i)⁻¹ • v_i`. Diagonal by construction. -/
def perturbedResolventOp (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ}
    (hV : V.IsHermitian) (s : ℂ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (perturbedEigenBasis μ hV).constr ℂ
    (fun i => (s + (perturbedEigenvalues μ hV i : ℂ))⁻¹ • perturbedEigenBasis μ hV i)

/-- **Gate 1, spectral bridge**: the trace of the constructed resolvent IS the
finite resolvent-trace function of the perturbed spectrum. -/
theorem perturbedResolventOp_trace (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (perturbedResolventOp μ hV s)
      = FstageFinite (perturbedEigenvalues μ hV) s := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (perturbedEigenBasis μ hV)]
  unfold FstageFinite
  first
    | rw [Matrix.trace]
    | rfl
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | (show (LinearMap.toMatrix (perturbedEigenBasis μ hV)
          (perturbedEigenBasis μ hV) (perturbedResolventOp μ hV s)) i i
        = (s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹
       rw [LinearMap.toMatrix_apply]
       unfold perturbedResolventOp
       rw [Basis.constr_basis, map_smul, Basis.repr_self]
       simp [Finsupp.single_apply])
    | (rw [Matrix.diag, LinearMap.toMatrix_apply]
       unfold perturbedResolventOp
       rw [Basis.constr_basis, map_smul, Basis.repr_self]
       simp [Finsupp.single_apply])
    | (simp [Matrix.diag, LinearMap.toMatrix_apply, perturbedResolventOp,
        Basis.constr_basis, Basis.repr_self, Finsupp.single_apply])

/-- The perturbed operator acts diagonally on the eigen-basis vectors. -/
theorem perturbedOp_apply_eigenBasis (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (i : Fin N) :
    perturbedOp μ V (perturbedEigenBasis μ hV i)
      = ((perturbedEigenvalues μ hV i : ℝ) : ℂ) • perturbedEigenBasis μ hV i := by
  have hbe : perturbedEigenBasis μ hV i
      = ((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i := by
    unfold perturbedEigenBasis
    first
      | rw [OrthonormalBasis.coe_toBasis]
      | simp [OrthonormalBasis.coe_toBasis]
  rw [hbe]
  have hev := (perturbedOp_isSymmetric μ hV).hasEigenvector_eigenvectorBasis
    perturbedOp_finrank i
  first
    | exact hev.apply_eq_smul
    | exact Module.End.HasEigenvector.apply_eq_smul hev
    | exact hev.1.apply_eq_smul

/-- **The constructed resolvent is a right inverse of `s•1 + H`** whenever the
shifted spectrum avoids zero — it deserves the name resolvent. -/
theorem resolvent_right_inverse (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (hne : ∀ i, s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0) :
    (s • LinearMap.id + perturbedOp μ V) ∘ₗ perturbedResolventOp μ hV s
      = LinearMap.id := by
  apply (perturbedEigenBasis μ hV).ext
  intro i
  rw [LinearMap.comp_apply]
  have h1 : perturbedResolventOp μ hV s (perturbedEigenBasis μ hV i)
      = (s + (perturbedEigenvalues μ hV i : ℂ))⁻¹ • perturbedEigenBasis μ hV i := by
    unfold perturbedResolventOp
    exact Basis.constr_basis _ _ _ _
  rw [h1, map_smul]
  set T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    s • LinearMap.id + perturbedOp μ V with hT
  have h2 : T (perturbedEigenBasis μ hV i)
      = (s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) • perturbedEigenBasis μ hV i := by
    rw [hT, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      perturbedOp_apply_eigenBasis μ hV i, ← add_smul]
  rw [h2, smul_smul, inv_mul_cancel₀ (hne i), one_smul, LinearMap.id_apply]

#print axioms perturbedResolventOp_trace
#print axioms perturbedOp_apply_eigenBasis
#print axioms resolvent_right_inverse

end

end RHFormalization
