import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- Rayleigh numerator on an eigenvector basis vector equals the eigenvalue. -/
theorem reInner_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    RCLike.re (inner 𝕜 (T (hT.eigenvectorBasis hn i)) (hT.eigenvectorBasis hn i))
      = hT.eigenvalues hn i := by
  rw [hT.apply_eigenvectorBasis hn i, inner_smul_left,
    (hT.eigenvectorBasis hn).inner_eq_one, mul_one, RCLike.conj_ofReal, RCLike.ofReal_re]

#print axioms reInner_eigenvectorBasis
end
end RHFormalization
