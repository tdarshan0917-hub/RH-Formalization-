import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Normed
import RHFormalization.FiniteStageSpectrum

/-!
# Gate 1: the finite prime-perturbed operator (free diagonal + Hermitian perturbation)

The first genuinely-PWQO finite object: `H_N = D + V` on `EuclideanSpace ℂ (Fin N)`,
where `D = diagonal(μ)` is the free part (nonneg real eigenvalues μ) and `V` is a
Hermitian perturbation matrix. We prove `H_N` is Hermitian.

This is the structural fix: the operator is free-diagonal PLUS a perturbation,
not free-only. Specializing `μ` to the Dirichlet eigenvalues and `V` to the prime
potential is a later substitution; Gate 1 establishes the right SHAPE.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex

variable {N : ℕ}

/-- The free diagonal matrix from a real eigenvalue vector. -/
noncomputable def freeDiag (μ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (μ i : ℂ))

/-- The free diagonal matrix is Hermitian (real diagonal entries). -/
theorem freeDiag_isHermitian (μ : Fin N → ℝ) :
    (freeDiag μ).IsHermitian := by
  unfold freeDiag IsHermitian
  ext i j
  simp only [conjTranspose_apply, diagonal_apply, star_apply]
  by_cases h : j = i
  · subst h; simp [Complex.conj_ofReal]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    simp

/-- **The finite perturbed operator matrix** `H_N = D + V`, with `D` the free
diagonal and `V` a Hermitian perturbation. -/
noncomputable def perturbedMatrix (μ : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  freeDiag μ + V

/-- The perturbed matrix is Hermitian when the perturbation is. -/
theorem perturbedMatrix_isHermitian (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) :
    (perturbedMatrix μ V).IsHermitian := by
  unfold perturbedMatrix
  exact (freeDiag_isHermitian μ).add hV

#print axioms freeDiag_isHermitian
#print axioms perturbedMatrix_isHermitian

end

end RHFormalization
