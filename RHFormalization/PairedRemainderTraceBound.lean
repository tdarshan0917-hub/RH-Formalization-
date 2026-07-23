-- SENTINEL: PREM-v6
import RHFormalization.GalerkinDuhamelTraceBound
import RHFormalization.GalerkinPairingBounds
import RHFormalization.AdmissibleColumnNormBound
import RHFormalization.AdmissibleResolventWeightSum
import Mathlib

/-!
# PairedRemainderTraceBound — B3 stone 1: the ABSTRACT N-free trace bound

Tr(D₁·A·D₂·B) with D₁,D₂ diagonal and A,B entrywise-bounded, bounded by
BA·BB·(Σ|d₁|)(Σ|d₂|) — no dimension factor. Instantiation is stone 2.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

open scoped BigOperators

variable {N : ℕ}

/-- Trace expansion for `D₁ · A · D₂ · B` with `D₁,D₂` diagonal. -/
theorem trace_diag_A_diag_B (A B : Matrix (Fin N) (Fin N) ℝ) (d₁ d₂ : Fin N → ℝ) :
    (Matrix.diagonal d₁ * A * Matrix.diagonal d₂ * B).trace
      = ∑ m, ∑ n, d₁ m * A m n * d₂ n * B n m := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try (refine Finset.sum_congr rfl (fun m _ => ?_)
       refine Finset.sum_congr rfl (fun n _ => ?_)
       ring)

/-- **THE ABSTRACT N-FREE BOUND.** -/
theorem abs_trace_diag_A_diag_B_le
    (A B : Matrix (Fin N) (Fin N) ℝ) (d₁ d₂ : Fin N → ℝ)
    (BA BB : ℝ) (hBA : 0 ≤ BA) (hBB : 0 ≤ BB)
    (hA : ∀ i j, |A i j| ≤ BA) (hB : ∀ i j, |B i j| ≤ BB) :
    |(Matrix.diagonal d₁ * A * Matrix.diagonal d₂ * B).trace|
      ≤ BA * BB * ((∑ m, |d₁ m|) * (∑ n, |d₂ n|)) := by
  classical
  rw [trace_diag_A_diag_B]
  have step1 : |∑ m, ∑ n, d₁ m * A m n * d₂ n * B n m|
      ≤ ∑ m, ∑ n, (BA * BB) * (|d₁ m| * |d₂ n|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun n _ => ?_)
    have e : |d₁ m * A m n * d₂ n * B n m|
        = |d₁ m| * |A m n| * |d₂ n| * |B n m| := by
      rw [abs_mul, abs_mul, abs_mul]
    rw [e]
    have hA' : |A m n| ≤ BA := hA m n
    have hB' : |B n m| ≤ BB := hB n m
    have hstep : |d₁ m| * |A m n| * |d₂ n| * |B n m|
        ≤ (BA * BB) * (|d₁ m| * |d₂ n|) := by
      have c1 : |d₁ m| * |A m n| * |d₂ n| * |B n m|
          ≤ |d₁ m| * BA * |d₂ n| * BB := by
        apply mul_le_mul _ hB' (abs_nonneg _) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hA' (abs_nonneg _)
      calc |d₁ m| * |A m n| * |d₂ n| * |B n m|
          ≤ |d₁ m| * BA * |d₂ n| * BB := c1
        _ = (BA * BB) * (|d₁ m| * |d₂ n|) := by ring
    exact hstep
  have step2 : (∑ m, ∑ n, (BA * BB) * (|d₁ m| * |d₂ n|))
      = BA * BB * ((∑ m, |d₁ m|) * (∑ n, |d₂ n|)) := by
    have inner : ∀ m : Fin N, (∑ n, (BA * BB) * (|d₁ m| * |d₂ n|))
        = (BA * BB) * |d₁ m| * ∑ n, |d₂ n| := by
      intro m
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    calc (∑ m, ∑ n, (BA * BB) * (|d₁ m| * |d₂ n|))
        = ∑ m, (BA * BB) * |d₁ m| * ∑ n, |d₂ n| :=
          Finset.sum_congr rfl (fun m _ => inner m)
      _ = (∑ m, (BA * BB) * |d₁ m|) * ∑ n, |d₂ n| := by
          rw [Finset.sum_mul]
      _ = (BA * BB) * (∑ m, |d₁ m|) * ∑ n, |d₂ n| := by
          rw [← Finset.mul_sum]
      _ = BA * BB * ((∑ m, |d₁ m|) * (∑ n, |d₂ n|)) := by ring
  exact le_trans step1 (le_of_eq step2)

#print axioms trace_diag_A_diag_B
#print axioms abs_trace_diag_A_diag_B_le

end RHFormalization
