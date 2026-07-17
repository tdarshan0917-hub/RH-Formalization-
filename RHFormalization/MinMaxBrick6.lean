import RHFormalization.MinMaxBrick5
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- Two subspaces whose dimensions sum to more than `dim E` intersect nontrivially. -/
theorem inf_ne_bot_of_finrank_add_gt (U W : Submodule 𝕜 E)
    (h : Module.finrank 𝕜 E < Module.finrank 𝕜 U + Module.finrank 𝕜 W) :
    U ⊓ W ≠ ⊥ := by
  intro hbot
  have key := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hbot] at key
  simp at key
  have hle : Module.finrank 𝕜 (U ⊔ W : Submodule 𝕜 E) ≤ Module.finrank 𝕜 E :=
    Submodule.finrank_le _
  omega

/-- The span of eigenvectors whose index lies in a finset `s`. -/
def eigenSpan (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (s : Finset (Fin n)) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : s => hT.eigenvectorBasis hn i))

/-- The eigenspan over `s` has dimension exactly `s.card`. -/
theorem finrank_eigenSpan (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (s : Finset (Fin n)) :
    Module.finrank 𝕜 (eigenSpan hT hn s) = s.card := by
  rw [eigenSpan, finrank_span_eq_card]
  · simp
  · exact (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective

/-- A vector in `eigenSpan s` is orthogonal to every eigenvector with index outside `s`. -/
theorem inner_eq_zero_of_mem_eigenSpan (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {s : Finset (Fin n)} {x : E} (hx : x ∈ eigenSpan hT hn s) {j : Fin n} (hj : j ∉ s) :
    inner 𝕜 (hT.eigenvectorBasis hn j) x = 0 := by
  rw [eigenSpan] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [(hT.eigenvectorBasis hn).orthonormal.2 ?_]
      rintro rfl
      exact hj i.2
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]

#print axioms inf_ne_bot_of_finrank_add_gt
#print axioms finrank_eigenSpan
#print axioms inner_eq_zero_of_mem_eigenSpan
end
end RHFormalization
