import RHFormalization.MinMaxBrick9

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {A B : E →ₗ[𝕜] E}

/-- **Weyl's eigenvalue perturbation inequality.** If two symmetric operators have Rayleigh
forms differing by at most `M·‖x‖²` pointwise, then each pair of eigenvalues (in sorted order)
differs by at most `M`. -/
theorem eigenvalues_dist_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (M : ℝ)
    (h : ∀ x : E, |RCLike.re (inner 𝕜 x (A x)) - RCLike.re (inner 𝕜 x (B x))| ≤ M * ‖x‖^2)
    (k : Fin n) :
    |hA.eigenvalues hn k - hB.eigenvalues hn k| ≤ M := by
  -- A ⪯ B + M·I  ⟹  λ_k(A) ≤ λ_k(B) + M
  have hAB : hA.eigenvalues hn k ≤ hB.eigenvalues hn k + M := by
    have hmono := eigenvalues_mono hA (shiftOp_symm hB M) hn ?_ k
    · rwa [eigenvalues_shiftOp hB hn M k] at hmono
    · intro x
      rw [shiftOp_rayleigh]
      have := abs_le.mp (h x)
      linarith [this.1, this.2]
  -- B ⪯ A + M·I  ⟹  λ_k(B) ≤ λ_k(A) + M
  have hBA : hB.eigenvalues hn k ≤ hA.eigenvalues hn k + M := by
    have hmono := eigenvalues_mono hB (shiftOp_symm hA M) hn ?_ k
    · rwa [eigenvalues_shiftOp hA hn M k] at hmono
    · intro x
      rw [shiftOp_rayleigh]
      have := abs_le.mp (h x)
      linarith [this.1, this.2]
  rw [abs_le]
  constructor <;> linarith

#print axioms eigenvalues_dist_le
end
end RHFormalization
