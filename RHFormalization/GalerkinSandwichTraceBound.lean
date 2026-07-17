import RHFormalization.GalerkinDuhamelTraceIdentity
import RHFormalization.GalerkinMatrices
import Mathlib

/-!
# Entrywise bound on the Dyson sandwich trace.

`Tr(M) = ∑_i M_ii`, so `|Tr(sandwich)| ≤ ∑_i |sandwich_ii|`. Foundational brick
for bounding `Tr(e^{-(t-u)K}·(-V)·e^{-u(K+V)})` toward the residual bound.
-/

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Matrix
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **Entrywise trace bound.** `|Tr(M)| ≤ ∑_i |M_ii|` for any matrix. -/
theorem abs_trace_le_sum_abs_diag (M : Matrix (Fin N) (Fin N) ℝ) :
    |M.trace| ≤ ∑ i, |M i i| := by
  rw [Matrix.trace]
  calc |∑ i, M.diag i| ≤ ∑ i, |M.diag i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |M i i| := rfl

#print axioms abs_trace_le_sum_abs_diag
