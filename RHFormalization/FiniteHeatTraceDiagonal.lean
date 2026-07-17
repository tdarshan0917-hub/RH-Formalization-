import RHFormalization.PerturbedTraceIdentity

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/--
Finite-dimensional heat trace for a diagonal matrix.

This is the first brick for replacing the current zero Duhamel/trace scaffold
with actual finite-stage matrix trace content.
-/
theorem matrix_trace_diagonal_heat_complex {N : ℕ}
    (lam : Fin N → ℂ) (t : ℂ) :
    Matrix.trace (Matrix.diagonal (fun i : Fin N => Complex.exp (-t * lam i))) =
      ∑ i : Fin N, Complex.exp (-t * lam i) := by
  rw [Matrix.trace_diagonal]

/--
Real-eigenvalue version used for nonnegative/self-adjoint finite stages.
-/
theorem matrix_trace_diagonal_heat_real {N : ℕ}
    (lam : Fin N → ℝ) (t : ℝ) :
    Matrix.trace
        (Matrix.diagonal
          (fun i : Fin N => Complex.exp (-(t : ℂ) * (lam i : ℂ)))) =
      ∑ i : Fin N, Complex.exp (-(t : ℂ) * (lam i : ℂ)) := by
  rw [Matrix.trace_diagonal]

#print axioms matrix_trace_diagonal_heat_complex
#print axioms matrix_trace_diagonal_heat_real

end

end RHFormalization
