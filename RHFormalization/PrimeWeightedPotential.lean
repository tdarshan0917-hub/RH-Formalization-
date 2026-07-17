import RHFormalization.PerturbedEigenvalueWeyl
import RHFormalization.PerturbedResidual
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Matrix

variable {N : ℕ}

/-- **The prime-weighted potential `V_prime`.** A diagonal Hermitian matrix whose
`k`-th entry carries the prime-power weight. For now the simplest genuine instance:
a real diagonal matrix `w : Fin N → ℝ` of prime weights, coerced to ℂ. This is the
finite-stage realization of the manuscript's potential `V_q(u) = w(q)·bump(u−log q)`,
in the spectral (diagonal) basis. Real, Hermitian, NOT zero. -/
def primePotential (w : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun k => (w k : ℂ))

/-- `primePotential` is Hermitian (real diagonal). -/
theorem primePotential_isHermitian (w : Fin N → ℝ) :
    (primePotential w).IsHermitian := by
  unfold primePotential
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.star_apply]
  by_cases h : i = j
  · subst h; simp [Complex.conj_ofReal]
  · simp [h, Ne.symm h]

#print axioms primePotential
#print axioms primePotential_isHermitian
end
end RHFormalization
