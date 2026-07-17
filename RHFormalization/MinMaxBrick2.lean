import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- Diagonal action: `⟨e_i, T x⟩ = λ_i · ⟨e_i, x⟩`. -/
theorem inner_eigenvectorBasis_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (x : E) (i : Fin n) :
    inner 𝕜 (hT.eigenvectorBasis hn i) (T x)
      = (hT.eigenvalues hn i : 𝕜) * inner 𝕜 (hT.eigenvectorBasis hn i) x := by
  rw [← hT (hT.eigenvectorBasis hn i) x, hT.apply_eigenvectorBasis hn i, inner_smul_left,
    RCLike.conj_ofReal]

/-- The full inner product `⟨x, T x⟩` expands diagonally as `∑ᵢ λᵢ · ⟨x,eᵢ⟩·⟨eᵢ,x⟩`. -/
theorem inner_self_eq_sum_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (x : E) :
    inner 𝕜 x (T x)
      = ∑ i, (hT.eigenvalues hn i : 𝕜)
          * (inner 𝕜 x (hT.eigenvectorBasis hn i) * inner 𝕜 (hT.eigenvectorBasis hn i) x) := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_eigenvectorBasis_apply hT hn x i]
  ring

#print axioms inner_eigenvectorBasis_apply
#print axioms inner_self_eq_sum_eigenvalues
end
end RHFormalization
