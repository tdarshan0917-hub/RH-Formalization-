import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Matrix

namespace RHFormalization

variable {N : ℕ}

/-- **Dyson step 1 (matrix heat-semigroup derivative).** For a complex matrix `A`,
the exponential semigroup `s ↦ exp(s·A)` has derivative `exp(t·A)·A` at `t`.
Variation-of-constants core of the Duhamel/Dyson expansion: with `A=-(K+V)` it
gives `d/dt e^{-t(K+V)} = -e^{-t(K+V)}(K+V)`. Uses `hasDerivAt_exp_smul_const`. -/
theorem hasDerivAt_matrix_exp_smul
    (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ℝ ((s : ℝ) • A))
      (NormedSpace.exp ℝ (t • A) * A) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
  simpa using h

#print axioms hasDerivAt_matrix_exp_smul

end RHFormalization
