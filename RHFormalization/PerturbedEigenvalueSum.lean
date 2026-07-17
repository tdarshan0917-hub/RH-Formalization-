import RHFormalization.PerturbedTraceIdentity
import Mathlib.LinearAlgebra.Trace

/-!
# Spectral eigenvalue-sum identity for the perturbed operator

`∑_i λ_i(H_N) = ∑_i μ_i + re(tr V)` — exact control of the eigenvalue sum,
no min-max. NOT full per-eigenvalue A.GROWTH (Courant–Fischer, absent from
Mathlib) and NOT Gate 4 (D.EXPORT). The trace-level spectral identity, honest.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex RCLike

variable {N : ℕ}

/-- The operator trace of `perturbedOp` equals the matrix trace. -/
theorem perturbedOp_trace_eq_matrix_trace (μ : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (perturbedOp μ V)
      = (perturbedMatrix μ V).trace := by
  unfold perturbedOp
  rw [Matrix.toEuclideanLin_eq_toLin]
  exact Matrix.trace_toLin_eq (perturbedMatrix μ V) (PiLp.basisFun 2 ℂ (Fin N))

/-- **Spectral eigenvalue-sum identity.**
`∑_i λ_i(H_N) = ∑_i μ_i + re(tr V)`. Exact control of the eigenvalue sum. -/
theorem perturbedEigenvalues_sum (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) :
    (∑ i, perturbedEigenvalues μ hV i)
      = (∑ i, μ i) + RCLike.re (V.trace) := by
  have hsym := perturbedOp_isSymmetric μ hV
  have h1 : RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (perturbedOp μ V))
      = ∑ i, perturbedEigenvalues μ hV i := by
    unfold perturbedEigenvalues
    exact hsym.re_trace_eq_sum_eigenvalues perturbedOp_finrank
  have h2 := perturbedOp_trace_eq_matrix_trace μ V
  have h3 := perturbedMatrix_trace μ V
  rw [← h1, h2, h3, map_add]
  have hre_sum : RCLike.re (∑ i, (μ i : ℂ)) = ∑ i, μ i := by
    push_cast
    simp
  rw [hre_sum]

#print axioms perturbedEigenvalues_sum

end

end RHFormalization
