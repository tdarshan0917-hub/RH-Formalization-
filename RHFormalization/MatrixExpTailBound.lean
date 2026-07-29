-- SENTINEL: EXPTAIL-v2
import RHFormalization.MatrixExpNormBound
import Mathlib

/-!
# MatrixExpTailBound — B3c stone 2

CONSUMER: stone 3 (Duhamel remainder control), en route to `h_ctail_le`.

  ‖exp A − 1 − A‖ ≤ e^{‖A‖} − 1 − ‖A‖

Both sides are the k ≥ 2 tails of their exponential series; compare termwise
via the banked `norm_pow_div_factorial_le`. No dimension factor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

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

/-- Algebra side: exp minus first two terms equals the k ≥ 2 tail. -/
theorem exp_sub_head_eq_tail (A : 𝔸) :
    NormedSpace.exp A - 1 - A
      = ∑' k : ℕ, (((k + 2).factorial : ℝ))⁻¹ • A ^ (k + 2) := by
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℝ))⁻¹ • A ^ k) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  have hsplit :
      (∑ k ∈ Finset.range 2, ((k.factorial : ℝ))⁻¹ • A ^ k)
        + (∑' k : ℕ, (((k + 2).factorial : ℝ))⁻¹ • A ^ (k + 2))
      = ∑' k : ℕ, ((k.factorial : ℝ))⁻¹ • A ^ k :=
    hsum.sum_add_tsum_nat_add 2
  have hhead :
      (∑ k ∈ Finset.range 2, ((k.factorial : ℝ))⁻¹ • A ^ k) = 1 + A := by
    simp [Finset.sum_range_succ]
  have hexp : NormedSpace.exp A = ∑' k : ℕ, ((k.factorial : ℝ))⁻¹ • A ^ k := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  rw [hexp, ← hsplit, hhead]
  abel

/-- Scalar side: e^x minus first two terms equals the k ≥ 2 tail. -/
theorem real_exp_sub_head_eq_tail (x : ℝ) :
    Real.exp x - 1 - x
      = ∑' k : ℕ, x ^ (k + 2) / (((k + 2).factorial : ℝ)) := by
  have hsum : Summable (fun k : ℕ => x ^ k / ((k.factorial : ℝ))) :=
    Real.summable_pow_div_factorial x
  have hsplit :
      (∑ k ∈ Finset.range 2, x ^ k / ((k.factorial : ℝ)))
        + (∑' k : ℕ, x ^ (k + 2) / (((k + 2).factorial : ℝ)))
      = ∑' k : ℕ, x ^ k / ((k.factorial : ℝ)) :=
    hsum.sum_add_tsum_nat_add 2
  have hexp : Real.exp x = ∑' k : ℕ, x ^ k / ((k.factorial : ℝ)) := by
    rw [Real.exp_eq_exp_ℝ]
    rw [NormedSpace.exp_eq_tsum_div]
  have hhead :
      (∑ k ∈ Finset.range 2, x ^ k / ((k.factorial : ℝ))) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [hexp, ← hsplit, hhead]
  ring

/-- **B3c stone 2: exponential-moment tail bound.**
`‖exp A − 1 − A‖ ≤ e^{‖A‖} − 1 − ‖A‖`. -/
theorem norm_exp_sub_one_sub_self_le (A : 𝔸) :
    ‖NormedSpace.exp A - 1 - A‖ ≤ Real.exp ‖A‖ - 1 - ‖A‖ := by
  rw [exp_sub_head_eq_tail, real_exp_sub_head_eq_tail]
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℝ))⁻¹ • A ^ k) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  have hnorm :
      Summable (fun k : ℕ => ‖(((k + 2).factorial : ℝ))⁻¹ • A ^ (k + 2)‖) :=
    ((NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) A).comp_injective
      (add_left_injective 2))
  have hmaj :
      Summable (fun k : ℕ => ‖A‖ ^ (k + 2) / (((k + 2).factorial : ℝ))) :=
    (Real.summable_pow_div_factorial ‖A‖).comp_injective
      (add_left_injective 2)
  calc
    ‖∑' k : ℕ, (((k + 2).factorial : ℝ))⁻¹ • A ^ (k + 2)‖
        ≤ ∑' k : ℕ, ‖(((k + 2).factorial : ℝ))⁻¹ • A ^ (k + 2)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖A‖ ^ (k + 2) / (((k + 2).factorial : ℝ)) :=
      Summable.tsum_le_tsum
        (fun k => norm_pow_div_factorial_le A (k + 2)) hnorm hmaj

end AbstractRing

section MatrixInstance

variable {N : ℕ}

/-- Matrix specialization at `t • A` — the form stone 3 consumes. -/
theorem matrix_norm_exp_smul_sub_head_le
    (hN : 0 < N) (t : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖NormedSpace.exp (t • A) - 1 - t • A‖
      ≤ Real.exp ‖t • A‖ - 1 - ‖t • A‖ := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact norm_exp_sub_one_sub_self_le (t • A)

#print axioms exp_sub_head_eq_tail
#print axioms norm_exp_sub_one_sub_self_le
#print axioms matrix_norm_exp_smul_sub_head_le

end MatrixInstance

end RHFormalization
