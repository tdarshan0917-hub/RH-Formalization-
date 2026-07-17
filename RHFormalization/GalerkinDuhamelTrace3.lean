import RHFormalization.GalerkinDuhamelTrace

/-!
# Brick 2, Path A1 rung 1: the order-3 Duhamel trace term
`Tr(V·diag(d₁)·V·diag(d₂)·V·diag(d₃)) = ∑_{i,k,j} V_{ij}·d₁_j·V_{jk}·d₂_k·V_{ki}·d₃_i`.
Order-3 of the Dyson expansion, generalizing stone 5 toward the full series.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Helper: `(M · diagonal d) i j = M i j * d j`. -/
theorem mul_diagonal_apply
    (M : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) (i j : Fin N) :
    (M * Matrix.diagonal d) i j = M i j * d j := by
  rw [Matrix.mul_apply]
  have : ∀ k, M i k * Matrix.diagonal d k j = if k = j then M i j * d j else 0 := by
    intro k; rw [Matrix.diagonal_apply]; split
    · next h => subst h; ring
    · ring
  simp only [this]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, if_true]

/-- Helper: `(V · diag d₁ · V) i k = ∑_j V_{ij}·d₁_j·V_{jk}`. -/
theorem V_diag_V_apply
    (V : Matrix (Fin N) (Fin N) ℝ) (d₁ : Fin N → ℝ) (i k : Fin N) :
    (V * Matrix.diagonal d₁ * V) i k = ∑ j, V i j * d₁ j * V j k := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_diagonal_apply]

/-- **Order-3 (core algebra)**: trace of `V·diag(d₁)·V·diag(d₂)·V·diag(d₃)`. -/
theorem trace_V_diag_V_diag_V_diag
    (V : Matrix (Fin N) (Fin N) ℝ) (d₁ d₂ d₃ : Fin N → ℝ) :
    (V * Matrix.diagonal d₁ * V * Matrix.diagonal d₂ * V * Matrix.diagonal d₃).trace
      = ∑ i, ∑ k, ∑ j, V i j * d₁ j * V j k * d₂ k * V k i * d₃ i := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply]
  rw [mul_diagonal_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (V * Matrix.diagonal d₁ * V * Matrix.diagonal d₂) i k
        = (V * Matrix.diagonal d₁ * V) i k * d₂ k from mul_diagonal_apply _ _ _ _]
  rw [V_diag_V_apply, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

#print axioms trace_V_diag_V_diag_V_diag
end
end RHFormalization
