import RHFormalization.MinMaxBrick2

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- The real part of `⟨x,e_i⟩·⟨e_i,x⟩` is `‖⟨e_i,x⟩‖²`. -/
theorem reTermInner_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (x : E) (i : Fin n) :
    RCLike.re (inner 𝕜 x (hT.eigenvectorBasis hn i) * inner 𝕜 (hT.eigenvectorBasis hn i) x)
      = ‖inner 𝕜 (hT.eigenvectorBasis hn i) x‖^2 := by
  rw [← inner_conj_symm (hT.eigenvectorBasis hn i) x, RCLike.mul_conj]
  simp
  exact norm_inner_symm _ _

/-- Each diagonal term's real part is `λ_i · ‖⟨e_i,x⟩‖²`. -/
theorem reTerm_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (x : E) (i : Fin n) :
    RCLike.re ((hT.eigenvalues hn i : 𝕜)
        * (inner 𝕜 x (hT.eigenvectorBasis hn i) * inner 𝕜 (hT.eigenvectorBasis hn i) x))
      = hT.eigenvalues hn i * ‖inner 𝕜 (hT.eigenvectorBasis hn i) x‖^2 := by
  rw [RCLike.re_ofReal_mul, reTermInner_eq hT hn x i]

/-- Rayleigh numerator as a real sum: `re⟨x,Tx⟩ = ∑ λ_i ‖⟨e_i,x⟩‖²`. -/
theorem reInner_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (x : E) :
    RCLike.re (inner 𝕜 x (T x))
      = ∑ i, hT.eigenvalues hn i * ‖inner 𝕜 (hT.eigenvectorBasis hn i) x‖^2 := by
  rw [inner_self_eq_sum_eigenvalues hT hn x, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact reTerm_eq hT hn x i

#print axioms reInner_eq_sum
end
end RHFormalization
