import RHFormalization.DNativeUnboundedOperator
import RHFormalization.PrimeWeightedPotential
import RHFormalization.PerturbedFormBound

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap

variable {N : ℕ}

/-- The prime operator `H₀ + V_prime + M·I` as a continuous linear map. -/
noncomputable def primeOpCLM (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
    (perturbedMatrix μ (primePotential w) + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))

/-- Its LinearPMap on the full domain. -/
noncomputable def primeOpPMap (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    EuclideanSpace ℂ (Fin N) →ₗ.[ℂ] EuclideanSpace ℂ (Fin N) :=
  (primeOpCLM μ w M).toPMap ⊤

/-- The prime operator matrix `H₀ + V_prime + M·I` is Hermitian. -/
theorem primeOpMatrix_isHermitian (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    (perturbedMatrix μ (primePotential w)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
  have h1 : (perturbedMatrix μ (primePotential w)).IsHermitian :=
    perturbedMatrix_isHermitian μ (primePotential_isHermitian w)
  have h2 : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp [Complex.conj_ofReal]
  exact h1.add h2

/-- The prime operator CLM is self-adjoint, since the matrix is Hermitian
and `toEuclideanCLM` is a ⋆-algebra equivalence. -/
theorem primeOpCLM_isSelfAdjoint (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    IsSelfAdjoint (primeOpCLM μ w M) := by
  have hH : IsSelfAdjoint (perturbedMatrix μ (primePotential w)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp (primeOpMatrix_isHermitian μ w M)
  unfold primeOpCLM
  rw [IsSelfAdjoint, ← map_star, hH.star_eq]

#print axioms primeOpMatrix_isHermitian
#print axioms primeOpCLM_isSelfAdjoint
end
end RHFormalization
