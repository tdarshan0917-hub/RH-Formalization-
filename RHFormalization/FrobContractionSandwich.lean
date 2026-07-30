-- SENTINEL: frob-contraction-sandwich-v1
import RHFormalization.TraceFrobeniusCS
import RHFormalization.FrobExpSemigroup
import RHFormalization.GalerkinPerturbedExpContraction
import Mathlib

/-!
# Core brick 6c′ — N-FREE Frobenius sandwich bound

Replaces the dimension-paying `frobSq_exp_neg_KV_le ≤ N` (6c-iii) route:
the contraction `expNeg_mulVec_sumSq_le` gives `frobSq (E * B) ≤ frobSq B`
columnwise, with NO dimension factor. Capstone:
`frobSq (E₁ * B * E₂) ≤ frobSq B`, both legs in the exact orientation of
QuadRemainderSandwichNormSplit.
DOWNSTREAM CONSUMER: |tr(D·(−V)·E₁·(−V)·E₂)| via abs_trace_mul_le_frob →
pointwise quadRemainder integrand bound, uniform along α → h_conv.
-/

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

/-- Frobenius square is transpose-invariant. -/
theorem frobSq_transpose (A : Matrix (Fin N) (Fin N) ℝ) :
    frobSq Aᵀ = frobSq A := by
  unfold frobSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.transpose_apply]

/-- Entry of a product as mulVec of a column. -/
theorem mul_apply_eq_mulVec_col
    (E B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (E * B) i j = E.mulVec (fun k => B k j) i := by
  first
    | simp [Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct]
    | simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    | rfl

/-- **Left contraction (N-free).** Nonneg form of `A` ⟹
`frobSq (exp (s•(−A)) * B) ≤ frobSq B`. -/
theorem frobSq_expNeg_mul_le
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N)
    (hform : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N, v m * v n * A m n)
    (B : Matrix (Fin N) (Fin N) ℝ) {s : ℝ} (hs : 0 ≤ s) :
    frobSq (NormedSpace.exp (s • (-A)) * B) ≤ frobSq B := by
  unfold frobSq
  rw [Finset.sum_comm]
  rw [show (∑ i : Fin N, ∑ j : Fin N, (B i j) ^ 2)
      = ∑ j : Fin N, ∑ i : Fin N, (B i j) ^ 2 from Finset.sum_comm]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hcol := expNeg_mulVec_sumSq_le A hN hform (fun k => B k j) hs
  calc ∑ i : Fin N, ((NormedSpace.exp (s • (-A)) * B) i j) ^ 2
      = ∑ i : Fin N,
          ((NormedSpace.exp (s • (-A))).mulVec (fun k => B k j) i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [mul_apply_eq_mulVec_col]
    _ ≤ ∑ i : Fin N, ((fun k => B k j) i) ^ 2 := hcol
    _ = ∑ i : Fin N, (B i j) ^ 2 := rfl

/-- Exp of `s•(−A)` is symmetric when `A` is. -/
theorem expNeg_smul_isSymm
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsSymm) (s : ℝ) :
    (NormedSpace.exp (s • (-A))).IsSymm := by
  have hSA : (s • (-A)).IsSymm := by
    first
      | exact (hA.neg).smul s
      | exact (hA.neg.smul s)
      | (unfold Matrix.IsSymm at *
         rw [Matrix.transpose_smul, Matrix.transpose_neg, hA])
  show (NormedSpace.exp (s • (-A)))ᵀ = NormedSpace.exp (s • (-A))
  first
    | rw [(Matrix.exp_transpose (s • (-A))).symm, hSA.eq]
    | rw [← Matrix.exp_transpose, hSA.eq]
    | rw [Matrix.exp_transpose, hSA.eq]

/-- **Right contraction (N-free).** Symmetric `A` with nonneg form ⟹
`frobSq (B * exp (s•(−A))) ≤ frobSq B`. -/
theorem frobSq_mul_expNeg_le
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N) (hA : A.IsSymm)
    (hform : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N, v m * v n * A m n)
    (B : Matrix (Fin N) (Fin N) ℝ) {s : ℝ} (hs : 0 ≤ s) :
    frobSq (B * NormedSpace.exp (s • (-A))) ≤ frobSq B := by
  have hE := expNeg_smul_isSymm A hA s
  calc frobSq (B * NormedSpace.exp (s • (-A)))
      = frobSq ((B * NormedSpace.exp (s • (-A)))ᵀ) :=
        (frobSq_transpose _).symm
    _ = frobSq ((NormedSpace.exp (s • (-A)))ᵀ * Bᵀ) := by
        rw [Matrix.transpose_mul]
    _ = frobSq (NormedSpace.exp (s • (-A)) * Bᵀ) := by
        rw [hE.eq]
    _ ≤ frobSq Bᵀ := frobSq_expNeg_mul_le A hN hform Bᵀ hs
    _ = frobSq B := frobSq_transpose B

/-- **CAPSTONE 6c′: the N-free sandwich.** Exact orientation of
QuadRemainderSandwichNormSplit: free leg `exp ((u−s)•(−K))` on the left,
perturbed leg `exp (s•(−(K+V)))` on the right. -/
theorem frobSq_sandwich_le
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hN : 0 < N)
    (hV : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n * galerkinV (N := N) δ qs w L m n)
    (B : Matrix (Fin N) (Fin N) ℝ)
    {u s : ℝ} (hus : 0 ≤ u - s) (hs : 0 ≤ s) :
    frobSq (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
        * B
        * NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))
      ≤ frobSq B := by
  have hKV := galerkinKV_isSymm (N := N) δ qs w L
  calc frobSq (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
        * B
        * NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))
      ≤ frobSq (NormedSpace.exp ((u - s) • -galerkinK (N := N) L) * B) :=
        frobSq_mul_expNeg_le _ hN hKV
          (galerkinKplusV_form_nonneg δ qs w L hV)
          (NormedSpace.exp ((u - s) • -galerkinK (N := N) L) * B) hs
    _ ≤ frobSq B :=
        frobSq_expNeg_mul_le _ hN (galerkinK_form_nonneg L) B hus

#print axioms frobSq_transpose
#print axioms mul_apply_eq_mulVec_col
#print axioms frobSq_expNeg_mul_le
#print axioms expNeg_smul_isSymm
#print axioms frobSq_mul_expNeg_le
#print axioms frobSq_sandwich_le
