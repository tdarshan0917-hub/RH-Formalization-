-- SENTINEL: frob-exp-semigroup-v1
import RHFormalization.TraceFrobeniusCS
import RHFormalization.GalerkinMatrices
import Mathlib

/-! # Core brick 6b — Frobenius norm of the symmetric semigroup.
For symmetric `S`: `frobSq (exp S) = Tr (exp (S + S))` — the identity
that hands the sandwich bound to the banked Feynman–Kac chain. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- 6b-i: `frobSq A = Tr (Aᵀ * A)`. -/
theorem frobSq_eq_trace_transpose_mul (A : Matrix (Fin N) (Fin N) ℝ) :
    frobSq A = (Aᵀ * A).trace := by
  unfold frobSq
  rw [Matrix.trace]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.transpose_apply]
  ring

/-- 6b-ii/iii: for symmetric `S`, `frobSq (exp S) = Tr (exp (S + S))`. -/
theorem frobSq_exp_symm_eq_trace_exp_double
    (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.IsSymm) :
    frobSq (NormedSpace.exp S) = (NormedSpace.exp (S + S)).trace := by
  rw [frobSq_eq_trace_transpose_mul]
  have hT : (NormedSpace.exp S)ᵀ = NormedSpace.exp S := by
    rw [(Matrix.exp_transpose S).symm]
    rw [hS.eq]
  rw [hT]
  have hsemi : NormedSpace.exp S * NormedSpace.exp S
      = NormedSpace.exp (S + S) := by
    first
      | exact (Matrix.exp_add_of_commute (Commute.refl S)).symm
      | exact (Matrix.exp_add_of_commute S S (Commute.refl S)).symm
      | exact (Matrix.exp_add_of_commute (A := S) (B := S) (Commute.refl S)).symm
      | exact (NormedSpace.exp_add_of_commute (Commute.refl S)).symm
      | (have h := Matrix.exp_add_of_commute (Commute.refl S)
         exact h.symm)
  rw [hsemi]

/-- `K + V` is symmetric (K diagonal, V banked symmetric). -/
theorem galerkinKV_isSymm (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    (galerkinK (N := N) L + galerkinV (N := N) δ qs w L).IsSymm := by
  have hV := galerkinV_symm (N := N) δ qs w L
  have hK : (galerkinK (N := N) L).IsSymm := by
    first
      | exact Matrix.isSymm_diagonal _
      | (unfold galerkinK; exact Matrix.isSymm_diagonal _)
      | (unfold Matrix.IsSymm galerkinK
         ext i j
         by_cases h : i = j <;> simp [Matrix.transpose_apply, h]
         <;> simp [Matrix.diagonal_apply, h, Ne.symm h])
  first
    | exact hK.add hV
    | (unfold Matrix.IsSymm at *
       rw [Matrix.transpose_add, hK, hV])

#print axioms frobSq_eq_trace_transpose_mul
#print axioms frobSq_exp_symm_eq_trace_exp_double
#print axioms galerkinKV_isSymm

end

end RHFormalization
