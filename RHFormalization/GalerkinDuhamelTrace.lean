import RHFormalization.GalerkinMatrices

/-!
# Brick 2, stone 5: the first Duhamel trace term (D.DUH2-FREE)
`Tr(V · diag(d₁) · V · diag(d₂)) = ∑_{m,n} V_{mn}·d₁_n·V_{nm}·d₂_m` —
the first genuinely non-commuting Duhamel trace (off-diagonal `V_{mn}·V_{nm}`).
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **Stone 5 (core)**: trace of `V · diag(d₁) · V · diag(d₂)` as a double sum. -/
theorem trace_V_diag_V_diag
    (V : Matrix (Fin N) (Fin N) ℝ) (d₁ d₂ : Fin N → ℝ) :
    (V * Matrix.diagonal d₁ * V * Matrix.diagonal d₂).trace
      = ∑ m, ∑ n, V m n * d₁ n * V n m * d₂ m := by
  -- Right-multiply by diag d₂: (A * diag d₂) i i = A i i * d₂ i
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro m _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  -- (V * diag d₁ * V) m k, then diagonal d₂ k m picks k = m
  have hdiag : ∀ k, (V * Matrix.diagonal d₁ * V) m k * Matrix.diagonal d₂ k m
      = if k = m then (V * Matrix.diagonal d₁ * V) m m * d₂ m else 0 := by
    intro k
    rw [Matrix.diagonal_apply]
    split
    · next h => subst h; ring
    · ring
  simp only [hdiag]
  rw [Finset.sum_ite_eq' Finset.univ m]
  simp only [Finset.mem_univ, if_true]
  -- now (V * diag d₁ * V) m m = ∑_n V_{mn} d₁_n V_{nm}
  rw [Matrix.mul_apply]
  have hinner : ∀ n, (V * Matrix.diagonal d₁) m n * V n m
      = V m n * d₁ n * V n m := by
    intro n
    rw [Matrix.mul_apply]
    have : ∀ k, V m k * Matrix.diagonal d₁ k n = if k = n then V m n * d₁ n else 0 := by
      intro k; rw [Matrix.diagonal_apply]; split
      · next h => subst h; ring
      · ring
    simp only [this]
    rw [Finset.sum_ite_eq' Finset.univ n]
    simp only [Finset.mem_univ, if_true]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [hinner]

#print axioms trace_V_diag_V_diag
end
end RHFormalization
