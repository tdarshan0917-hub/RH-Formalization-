-- SENTINEL: frob-submultiplicative-v2
import RHFormalization.TraceFrobeniusCS
import Mathlib

/-! # Core brick 6c-i — Frobenius submultiplicativity.
`frobSq (A*B) ≤ frobSq A * frobSq B` via per-entry Cauchy–Schwarz. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

theorem frobSq_mul_le (A B : Matrix (Fin N) (Fin N) ℝ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  unfold frobSq
  have hentry : ∀ i j : Fin N, ((A * B) i j) ^ 2
      ≤ (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    first
      | exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun k => A i k) (fun k => B k j)
      | exact Finset.inner_mul_le_norm_mul_norm Finset.univ
          (fun k => A i k) (fun k => B k j)
  calc (∑ i, ∑ j, ((A * B) i j) ^ 2)
      ≤ ∑ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact Finset.sum_le_sum (fun j _ => hentry i j)
    _ = (∑ i, ∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, (A i j) ^ 2) * (∑ i, ∑ j, (B i j) ^ 2) := by
        congr 1
        exact Finset.sum_comm

#print axioms frobSq_mul_le

end

end RHFormalization
