-- SENTINEL: trace-frobenius-cs-v2
import Mathlib

/-! # Core brick 6a — Frobenius–Cauchy–Schwarz for the real matrix trace.
`|Tr(A·B)| ≤ √(frobSq A) · √(frobSq B)`. Self-contained. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Squared Frobenius norm as an entry sum. -/
def frobSq (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

theorem frobSq_nonneg (A : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  positivity

/-- Trace of a product as a double entry sum. -/
theorem trace_mul_eq_double_sum (A B : Matrix (Fin N) (Fin N) ℝ) :
    (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]

/-- **Brick 6a: trace Cauchy–Schwarz.** -/
theorem abs_trace_mul_le_frob (A B : Matrix (Fin N) (Fin N) ℝ) :
    |(A * B).trace| ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := by
  rw [trace_mul_eq_double_sum]
  -- flatten to the product type
  have hflat : (∑ i, ∑ j, A i j * B j i)
      = ∑ p : Fin N × Fin N, A p.1 p.2 * B p.2 p.1 := by
    first
      | (rw [Fintype.sum_prod_type])
      | (rw [← Fintype.sum_prod_type])
      | (exact (Fintype.sum_prod_type _).symm)
  have hAflat : frobSq A = ∑ p : Fin N × Fin N, (A p.1 p.2) ^ 2 := by
    unfold frobSq
    first
      | (rw [Fintype.sum_prod_type])
      | (rw [← Fintype.sum_prod_type])
      | (exact (Fintype.sum_prod_type _).symm)
  have hBflat : frobSq B = ∑ p : Fin N × Fin N, (B p.2 p.1) ^ 2 := by
    unfold frobSq
    have hswap : (∑ i, ∑ j, (B i j) ^ 2) = ∑ j, ∑ i, (B i j) ^ 2 :=
      Finset.sum_comm
    rw [hswap]
    first
      | (rw [Fintype.sum_prod_type])
      | (rw [← Fintype.sum_prod_type])
      | (exact (Fintype.sum_prod_type _).symm)
  rw [hflat]
  set T := ∑ p : Fin N × Fin N, A p.1 p.2 * B p.2 p.1 with hT
  have hCS : T ^ 2 ≤ (∑ p : Fin N × Fin N, (A p.1 p.2) ^ 2)
      * (∑ p : Fin N × Fin N, (B p.2 p.1) ^ 2) := by
    first
      | exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun p => A p.1 p.2) (fun p => B p.2 p.1)
      | exact Finset.inner_mul_le_norm_mul_norm Finset.univ
          (fun p => A p.1 p.2) (fun p => B p.2 p.1)
      | (have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun p : Fin N × Fin N => A p.1 p.2)
            (fun p : Fin N × Fin N => B p.2 p.1)
         first
           | exact h
           | (convert h using 2 <;> ring))
      | (have h := Finset.sum_sq_le_sq_mul_sq Finset.univ
            (fun p : Fin N × Fin N => A p.1 p.2)
            (fun p : Fin N × Fin N => B p.2 p.1)
         first
           | exact h
           | (convert h using 2 <;> ring))
  have hSA : (0:ℝ) ≤ ∑ p : Fin N × Fin N, (A p.1 p.2) ^ 2 := by positivity
  have hSB : (0:ℝ) ≤ ∑ p : Fin N × Fin N, (B p.2 p.1) ^ 2 := by positivity
  have habs : |T| = Real.sqrt (T ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs, hAflat, hBflat, ← Real.sqrt_mul hSA]
  exact Real.sqrt_le_sqrt hCS

#print axioms frobSq_nonneg
#print axioms trace_mul_eq_double_sum
#print axioms abs_trace_mul_le_frob

end

end RHFormalization
