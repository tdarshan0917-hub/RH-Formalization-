import Mathlib
import RHFormalization.EnvDomShellPosExp
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, u>0 per-term factorization.** Each shell term factors the
`e^{u/2}` growth out, leaving a `j = k−u` Gaussian:
`(k+1)·e^{k/2}·e^{-κ'(u−k)²} ≤ e^{u/2}·e^{1/(16κ')}·(k+1)·e^{-κ'(u−k)²}·e^{... }`.
More usefully, using the exponent bound directly:
`(k+1)·e^{k/2}·e^{-κ'(u−k)²} ≤ (k+1)·e^{u/2 + 1/(16κ')}` — but this loses the
`k`-decay. Instead we keep it multiplicative: the term equals
`(k+1)·exp(k/2 − κ'(u−k)²)`, bounded by `(k+1)·exp(u/2 + 1/(16κ'))`. -/
theorem shell_pos_term_factor
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      = ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2 - κ' * (u - (k : ℝ)) ^ 2) := by
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

#print axioms shell_pos_term_factor

end RHFormalization
