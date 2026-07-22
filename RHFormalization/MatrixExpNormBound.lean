-- SENTINEL: EXPNORM-v5
import Mathlib

/-!
# MatrixExpNormBound — B3c foundation stone 1

Proves the Banach-algebra estimate

  ‖exp A‖ ≤ exp ‖A‖

and specializes it to real square matrices equipped with the repository's
L∞ operator norm.

The proof compares the exponential series term-by-term. No dimension factor
is introduced.
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

section AbstractRing

variable {𝔸 : Type*}
  [NormedRing 𝔸]
  [NormOneClass 𝔸]
  [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

/-- The scalar exponential majorant is summable. -/
theorem expSeries_norm_summable (A : 𝔸) :
    Summable (fun k : ℕ => ‖A‖ ^ k / (k.factorial : ℝ)) := by
  simpa using Real.summable_pow_div_factorial ‖A‖

/-- Termwise estimate for the exponential series. -/
theorem norm_pow_div_factorial_le (A : 𝔸) (k : ℕ) :
    ‖(k.factorial : ℝ)⁻¹ • A ^ k‖
      ≤ ‖A‖ ^ k / (k.factorial : ℝ) := by
  have hpow : ‖A ^ k‖ ≤ ‖A‖ ^ k := by
    induction k with
    | zero =>
        simp
    | succ m ih =>
        calc
          ‖A ^ (m + 1)‖
              = ‖A ^ m * A‖ := by rw [pow_succ]
          _ ≤ ‖A ^ m‖ * ‖A‖ := norm_mul_le _ _
          _ ≤ ‖A‖ ^ m * ‖A‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg A)
          _ = ‖A‖ ^ (m + 1) := by rw [pow_succ]

  have hscalar :
      ‖((k.factorial : ℝ)⁻¹ : ℝ)‖
        = (k.factorial : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity

  rw [norm_smul, hscalar, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- **Banach-algebra exponential bound:** `‖exp A‖ ≤ e^{‖A‖}`. -/
theorem norm_exp_le (A : 𝔸) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  rw [NormedSpace.exp_eq_tsum ℝ]

  have hnorm :
      Summable
        (fun k : ℕ =>
          ‖(k.factorial : ℝ)⁻¹ • A ^ k‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) A

  have hmaj :
      Summable
        (fun k : ℕ =>
          ‖A‖ ^ k / (k.factorial : ℝ)) :=
    expSeries_norm_summable A

  calc
    ‖∑' k : ℕ, (k.factorial : ℝ)⁻¹ • A ^ k‖
        ≤ ∑' k : ℕ, ‖(k.factorial : ℝ)⁻¹ • A ^ k‖ :=
      norm_tsum_le_tsum_norm hnorm

    _ ≤ ∑' k : ℕ, ‖A‖ ^ k / (k.factorial : ℝ) :=
      Summable.tsum_le_tsum
        (fun k => norm_pow_div_factorial_le A k)
        hnorm
        hmaj

    _ = Real.exp ‖A‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      apply tsum_congr
      intro k
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

end AbstractRing

section MatrixInstance

variable {N : ℕ}

/--
Matrix specialization in the repository's L∞ operator norm.

`0 < N` supplies the nonempty index type required by the matrix normed-ring
instance.
-/
theorem matrix_norm_exp_le
    (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact norm_exp_le A

/-- Scaled matrix-exponential estimate. -/
theorem matrix_norm_exp_smul_le
    (hN : 0 < N)
    (t : ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖NormedSpace.exp (t • A)‖
      ≤ Real.exp (|t| * ‖A‖) := by
  refine le_trans (matrix_norm_exp_le hN (t • A)) ?_
  apply Real.exp_le_exp.mpr
  rw [norm_smul, Real.norm_eq_abs]

#print axioms norm_exp_le
#print axioms matrix_norm_exp_le
#print axioms matrix_norm_exp_smul_le

end MatrixInstance

end RHFormalization
