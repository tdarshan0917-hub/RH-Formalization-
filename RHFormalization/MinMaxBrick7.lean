import RHFormalization.MinMaxBrick6

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {A B : E →ₗ[𝕜] E}

theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  rw [show (Finset.univ.filter (fun i : Fin n => i ≤ k)) = Finset.Iic k by ext i; simp,
    Fin.card_Iic]

theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  rw [show (Finset.univ.filter (fun i : Fin n => k ≤ i)) = Finset.Ici k by ext i; simp,
    Fin.card_Ici]

/-- **Eigenvalue monotonicity (Courant–Fischer).** If `A` and `B` are symmetric operators with
`re⟨x, A x⟩ ≤ re⟨x, B x⟩` for all `x` (i.e. `A ⪯ B` in form order), then for every index `k`
the `k`-th eigenvalues satisfy `λ_k(A) ≤ λ_k(B)`. -/
theorem eigenvalues_mono (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
    (hAB : ∀ x : E, RCLike.re (inner 𝕜 x (A x)) ≤ RCLike.re (inner 𝕜 x (B x)))
    (k : Fin n) :
    hA.eigenvalues hn k ≤ hB.eigenvalues hn k := by
  -- U = A's top (k+1) eigenspace, W = B's bottom (n-k) eigenspace
  set U := eigenSpan hA hn (Finset.univ.filter (fun i : Fin n => i ≤ k)) with hU
  set W := eigenSpan hB hn (Finset.univ.filter (fun i : Fin n => k ≤ i)) with hW
  have hdimU : Module.finrank 𝕜 U = (k : ℕ) + 1 := by
    rw [hU, finrank_eigenSpan, card_filter_le]
  have hdimW : Module.finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_eigenSpan, card_filter_ge]
  -- dims sum to n+1 > n, so they intersect nontrivially
  have hkn : (k : ℕ) < n := k.2
  have hgt : Module.finrank 𝕜 E < Module.finrank 𝕜 U + Module.finrank 𝕜 W := by
    rw [hdimU, hdimW, hn]; omega
  have hne := inf_ne_bot_of_finrank_add_gt U W hgt
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hxmem
  obtain ⟨hxU, hxW⟩ := hxmem
  have hxnorm : (0:ℝ) < ‖x‖^2 := by positivity
  -- x ∈ U = A's top eigenspace: orthogonal to e^A_j for j > k → lower half for A
  have hAlow : (hA.eigenvalues hn k) * ‖x‖^2 ≤ RCLike.re (inner 𝕜 x (A x)) := by
    apply rayleigh_ge_on_top_eigenspace hA hn k
    intro j hj
    apply inner_eq_zero_of_mem_eigenSpan hA hn hxU
    simp; omega
  -- x ∈ W = B's bottom eigenspace: orthogonal to e^B_j for j < k → upper half for B
  have hBup : RCLike.re (inner 𝕜 x (B x)) ≤ (hB.eigenvalues hn k) * ‖x‖^2 := by
    apply rayleigh_le_on_bot_eigenspace hB hn k
    intro j hj
    apply inner_eq_zero_of_mem_eigenSpan hB hn hxW
    simp; omega
  -- chain: λ_k(A)‖x‖² ≤ ⟨x,Ax⟩ ≤ ⟨x,Bx⟩ ≤ λ_k(B)‖x‖²
  have hchain : (hA.eigenvalues hn k) * ‖x‖^2 ≤ (hB.eigenvalues hn k) * ‖x‖^2 :=
    le_trans hAlow (le_trans (hAB x) hBup)
  exact le_of_mul_le_mul_right hchain hxnorm

#print axioms eigenvalues_mono
end
end RHFormalization
