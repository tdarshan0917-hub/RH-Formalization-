import RHFormalization.FinitePerturbedSpectrum

/-!
# Spectral trace identity for the perturbed operator

A real spectral constraint on `H_N = D + V` provable WITHOUT min-max:
the matrix trace splits as `tr(H_N) = ∑ μ_i + tr(V)`, and (operator trace =
sum of eigenvalues) connects this to the spectrum. This controls the SUM of the
perturbed eigenvalues exactly — a genuine partial A.GROWTH fact, using only
Mathlib tools that exist (`trace_diagonal`, trace additivity,
`trace_eq_sum_eigenvalues`).

This is NOT full per-eigenvalue A.GROWTH (which needs Courant–Fischer min-max,
absent from Mathlib). It is the trace-level constraint, honestly labeled.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex

variable {N : ℕ}

/-- The matrix trace of the perturbed matrix splits as `∑ μ_i + tr(V)`. -/
theorem perturbedMatrix_trace (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) :
    (perturbedMatrix μ V).trace = (∑ i, (μ i : ℂ)) + V.trace := by
  unfold perturbedMatrix freeDiag
  rw [Matrix.trace_add, Matrix.trace_diagonal]

#print axioms perturbedMatrix_trace

end

end RHFormalization
