import Mathlib

/-!
# A.ENV-DOM, brick 1: von Mangoldt weight bound (manuscript p53, termwise).

For a prime power q, Lambda(q) = log p <= log q. Hence Lambda(q)/q <= (log q)/q.
This is the per-term weight that the logarithmic-shell sum aggregates. Elementary,
no zeta input. First green brick at the FLOOR of the operator nonnegativity.
-/

namespace RHFormalization
open scoped BigOperators

/-- Lambda(q) <= log q for every q (von Mangoldt is log p on prime powers, 0 else; log p <= log q). -/
theorem vonMangoldt_le_log (q : ℕ) :
    ArithmeticFunction.vonMangoldt q ≤ Real.log q := by
  exact ArithmeticFunction.vonMangoldt_le_log

#print axioms vonMangoldt_le_log

end RHFormalization
