import RHFormalization.GalerkinDuhamel1Term
import Mathlib

namespace RHFormalization

open scoped BigOperators

/--
Gate replacement for the failed Matrix.exp route.

Instead of using general `Matrix.exp`, define the free heat matrix directly
as the diagonal matrix with entries `heatWeight L t i`.
-/
noncomputable def galerkinFreeHeatDiagonal {N : ℕ} (L t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i : Fin N => heatWeight L t i)

/-- Diagonal entries are exactly the heat weights. -/
theorem galerkinFreeHeatDiagonal_apply_same {N : ℕ} (L t : ℝ) (i : Fin N) :
    galerkinFreeHeatDiagonal (N := N) L t i i = heatWeight L t i := by
  simp [galerkinFreeHeatDiagonal]

/-- Off-diagonal entries vanish. -/
theorem galerkinFreeHeatDiagonal_apply_ne {N : ℕ} (L t : ℝ) {i j : Fin N} (hij : i ≠ j) :
    galerkinFreeHeatDiagonal (N := N) L t i j = 0 := by
  simp [galerkinFreeHeatDiagonal, hij]

/--
Surface theorem: the old Matrix.exp-based free heat should be replaceable by
this diagonal heat matrix in every Duhamel trace formula.
-/
theorem galerkinFreeHeatDiagonal_trace_weight {N : ℕ} (L t : ℝ) :
    Matrix.trace (galerkinFreeHeatDiagonal (N := N) L t)
      =
    ∑ i : Fin N, heatWeight L t i := by
  simp [galerkinFreeHeatDiagonal, Matrix.trace]

#print axioms galerkinFreeHeatDiagonal
#print axioms galerkinFreeHeatDiagonal_apply_same
#print axioms galerkinFreeHeatDiagonal_apply_ne
#print axioms galerkinFreeHeatDiagonal_trace_weight

end RHFormalization
