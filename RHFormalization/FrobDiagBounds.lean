-- SENTINEL: frob-diag-bounds-v1
import RHFormalization.FrobSubmultiplicative
import RHFormalization.SpikeTransferRateM1
import Mathlib

/-! # Core brick 6c-ii — frobSq of the diagonal heat factor and of V's negation. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

theorem frobSq_neg (A : Matrix (Fin N) (Fin N) ℝ) : frobSq (-A) = frobSq A := by
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.neg_apply]
  ring

theorem frobSq_diagonal (d : Fin N → ℝ) :
    frobSq (Matrix.diagonal d) = ∑ i, (d i) ^ 2 := by
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne' d hj]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- frobSq of the heat diagonal is at most `N` for nonnegative time. -/
theorem frobSq_heat_diagonal_le (L t : ℝ) (ht : 0 ≤ t) :
    frobSq (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L t m))
      ≤ (N : ℝ) := by
  rw [frobSq_diagonal]
  have h1 : ∀ m : Fin N, (heatWeight (N := N) L t m) ^ 2 ≤ 1 := by
    intro m
    have hle := heatWeight_le_one (N := N) L t ht m
    have hnn : 0 ≤ heatWeight (N := N) L t m := by
      unfold heatWeight
      exact le_of_lt (Real.exp_pos _)
    nlinarith
  calc (∑ m : Fin N, (heatWeight (N := N) L t m) ^ 2)
      ≤ ∑ _m : Fin N, (1:ℝ) := Finset.sum_le_sum (fun m _ => h1 m)
    _ = (N : ℝ) := by simp

#print axioms frobSq_neg
#print axioms frobSq_diagonal
#print axioms frobSq_heat_diagonal_le

end

end RHFormalization
