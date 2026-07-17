import RHFormalization.DNativeUnboundedOperator
import RHFormalization.DecodedGalerkinFStageForwardGate
import RHFormalization.PrimeWeightedPotential
import RHFormalization.PerturbedFormBound

-- SENTINEL: decoded-native-stage-v1

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap

variable {N : ℕ}

/-- The prime operator `H₀ + V_prime + M·I` as a continuous linear map. -/
noncomputable def decodedGalerkinOpCLM (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
    (perturbedMatrix μ (decodedGalerkinVC (N := N) δ qs w L) + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))

/-- Its LinearPMap on the full domain. -/
noncomputable def decodedGalerkinOpPMap (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    EuclideanSpace ℂ (Fin N) →ₗ.[ℂ] EuclideanSpace ℂ (Fin N) :=
  (decodedGalerkinOpCLM μ δ qs w L M).toPMap ⊤

/-- The prime operator matrix `H₀ + V_prime + M·I` is Hermitian. -/
theorem decodedGalerkinOpMatrix_isHermitian (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    (perturbedMatrix μ (decodedGalerkinVC (N := N) δ qs w L)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
  have h1 : (perturbedMatrix μ (decodedGalerkinVC (N := N) δ qs w L)).IsHermitian :=
    perturbedMatrix_isHermitian μ (decodedGalerkinVC_isHermitian (N := N) δ qs w L)
  have h2 : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp [Complex.conj_ofReal]
  exact h1.add h2

/-- The prime operator CLM is self-adjoint, since the matrix is Hermitian
and `toEuclideanCLM` is a ⋆-algebra equivalence. -/
theorem decodedGalerkinOpCLM_isSelfAdjoint (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    IsSelfAdjoint (decodedGalerkinOpCLM μ δ qs w L M) := by
  have hH : IsSelfAdjoint (perturbedMatrix μ (decodedGalerkinVC (N := N) δ qs w L)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp (decodedGalerkinOpMatrix_isHermitian μ δ qs w L M)
  unfold decodedGalerkinOpCLM
  rw [IsSelfAdjoint, ← map_star, hH.star_eq]

#print axioms decodedGalerkinOpMatrix_isHermitian
#print axioms decodedGalerkinOpCLM_isSelfAdjoint
end
end RHFormalization
