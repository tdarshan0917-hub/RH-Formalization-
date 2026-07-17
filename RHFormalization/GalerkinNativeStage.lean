import RHFormalization.DNativeUnboundedOperator
import RHFormalization.GalerkinFStageForwardGate
import RHFormalization.PrimeWeightedPotential
import RHFormalization.PerturbedFormBound

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap

variable {N : ℕ}

/-- The prime operator `H₀ + V_prime + M·I` as a continuous linear map. -/
noncomputable def galerkinOpCLM (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
    (perturbedMatrix μ (galerkinVC (N := N) δ qs w L) + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))

/-- Its LinearPMap on the full domain. -/
noncomputable def galerkinOpPMap (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    EuclideanSpace ℂ (Fin N) →ₗ.[ℂ] EuclideanSpace ℂ (Fin N) :=
  (galerkinOpCLM μ δ qs w L M).toPMap ⊤

/-- The prime operator matrix `H₀ + V_prime + M·I` is Hermitian. -/
theorem galerkinOpMatrix_isHermitian (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    (perturbedMatrix μ (galerkinVC (N := N) δ qs w L)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
  have h1 : (perturbedMatrix μ (galerkinVC (N := N) δ qs w L)).IsHermitian :=
    perturbedMatrix_isHermitian μ (galerkinVC_isHermitian (N := N) δ qs w L)
  have h2 : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp [Complex.conj_ofReal]
  exact h1.add h2

/-- The prime operator CLM is self-adjoint, since the matrix is Hermitian
and `toEuclideanCLM` is a ⋆-algebra equivalence. -/
theorem galerkinOpCLM_isSelfAdjoint (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    IsSelfAdjoint (galerkinOpCLM μ δ qs w L M) := by
  have hH : IsSelfAdjoint (perturbedMatrix μ (galerkinVC (N := N) δ qs w L)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp (galerkinOpMatrix_isHermitian μ δ qs w L M)
  unfold galerkinOpCLM
  rw [IsSelfAdjoint, ← map_star, hH.star_eq]

#print axioms galerkinOpMatrix_isHermitian
#print axioms galerkinOpCLM_isSelfAdjoint
end
end RHFormalization
