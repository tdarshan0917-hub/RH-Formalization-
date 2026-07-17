import RHFormalization.MinMaxBrick3

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- Parseval in eigenbasis: `∑ ‖⟨e_i,x⟩‖² = ‖x‖²`. -/
theorem sum_norm_sq_inner (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (x : E) :
    ∑ i, ‖inner 𝕜 (hT.eigenvectorBasis hn i) x‖^2 = ‖x‖^2 := by
  have h := (hT.eigenvectorBasis hn).sum_inner_mul_inner x x
  have h2 : RCLike.re (inner 𝕜 x x) = ∑ i, ‖inner 𝕜 (hT.eigenvectorBasis hn i) x‖^2 := by
    rw [← h, map_sum]
    exact Finset.sum_congr rfl (fun i _ => reTermInner_eq hT hn x i)
  rw [← h2, inner_self_eq_norm_sq]

/-- **Lower Courant–Fischer half.** If `x` is orthogonal to every eigenvector with index
strictly above `k` in eigenvalue order (so `x` lies in the top `k+1` eigenspace), then the
Rayleigh numerator is at least `λ_k · ‖x‖²`. -/
theorem rayleigh_ge_on_top_eigenspace (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (k : Fin n) {x : E}
    (hx : ∀ i : Fin n, k < i → inner 𝕜 (hT.eigenvectorBasis hn i) x = 0) :
    (hT.eigenvalues hn k) * ‖x‖^2 ≤ RCLike.re (inner 𝕜 x (T x)) := by
  rw [reInner_eq_sum hT hn x, ← sum_norm_sq_inner hT hn x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rcases le_or_gt i k with hik | hik
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hik) (sq_nonneg _)
  · rw [hx i hik]; simp

#print axioms rayleigh_ge_on_top_eigenspace
end
end RHFormalization
