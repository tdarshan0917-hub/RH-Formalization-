import RHFormalization.MinMaxBrick4

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- **Upper Courant–Fischer half.** If `x` is orthogonal to every eigenvector with index
strictly below `k` in eigenvalue order (so `x` lies in the bottom `n−k` eigenspace), then the
Rayleigh numerator is at most `λ_k · ‖x‖²`. -/
theorem rayleigh_le_on_bot_eigenspace (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (k : Fin n) {x : E}
    (hx : ∀ i : Fin n, i < k → inner 𝕜 (hT.eigenvectorBasis hn i) x = 0) :
    RCLike.re (inner 𝕜 x (T x)) ≤ (hT.eigenvalues hn k) * ‖x‖^2 := by
  rw [reInner_eq_sum hT hn x, ← sum_norm_sq_inner hT hn x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rcases lt_or_ge i k with hik | hik
  · rw [hx i hik]; simp
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hik) (sq_nonneg _)

#print axioms rayleigh_le_on_bot_eigenspace
end
end RHFormalization
