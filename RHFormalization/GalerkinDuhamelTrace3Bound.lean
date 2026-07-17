import RHFormalization.GalerkinDuhamelTrace3
import RHFormalization.GalerkinDuhamelTraceBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/--
Abstract order-3 all-free trace estimate from a uniform entrywise
bound on the inserted matrix.

This theorem is consumed by
`abs_trace_neg_galerkinV_diag3_le`
to discharge the scalar nested-sum estimate for the order-3
all-free Duhamel word.
-/
theorem abs_trace_V_diag_V_diag_V_diag_le
    (V : Matrix (Fin N) (Fin N) ℝ)
    (d₁ d₂ d₃ : Fin N → ℝ)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hV : ∀ i j, |V i j| ≤ B) :
    |(
      V * Matrix.diagonal d₁
        * V * Matrix.diagonal d₂
        * V * Matrix.diagonal d₃
    ).trace|
      ≤
    B ^ 3 *
      ((∑ j, |d₁ j|)
        * (∑ k, |d₂ k|)
        * (∑ i, |d₃ i|)) := by
  classical

  rw [trace_V_diag_V_diag_V_diag]

  calc
    |∑ i, ∑ k, ∑ j,
        V i j * d₁ j * V j k * d₂ k * V k i * d₃ i|
        ≤
      ∑ i,
        |∑ k, ∑ j,
          V i j * d₁ j * V j k * d₂ k * V k i * d₃ i| :=
      Finset.abs_sum_le_sum_abs _ _

    _ ≤
      ∑ i, ∑ k,
        |∑ j,
          V i j * d₁ j * V j k * d₂ k * V k i * d₃ i| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _

    _ ≤
      ∑ i, ∑ k, ∑ j,
        |V i j * d₁ j * V j k * d₂ k * V k i * d₃ i| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact Finset.abs_sum_le_sum_abs _ _

    _ ≤
      ∑ i, ∑ k, ∑ j,
        B ^ 3 * (|d₁ j| * |d₂ k| * |d₃ i|) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _

      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]

      have hbound :
          |V i j| * |d₁ j| * |V j k| * |d₂ k|
              * |V k i| * |d₃ i|
            ≤
          B * |d₁ j| * B * |d₂ k| * B * |d₃ i| := by
        gcongr
        · exact hV i j
        · exact hV j k
        · exact hV k i

      calc
        |V i j| * |d₁ j| * |V j k| * |d₂ k|
              * |V k i| * |d₃ i|
            ≤
          B * |d₁ j| * B * |d₂ k| * B * |d₃ i| :=
          hbound

        _ =
          B ^ 3 * (|d₁ j| * |d₂ k| * |d₃ i|) := by
          ring

    _ =
      ∑ i, ∑ k,
        (B ^ 3 * |d₂ k| * |d₃ i|)
          * (∑ j, |d₁ j|) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

    _ =
      ∑ i,
        (B ^ 3 * |d₃ i| * (∑ j, |d₁ j|))
          * (∑ k, |d₂ k|) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

    _ =
      (B ^ 3
          * (∑ j, |d₁ j|)
          * (∑ k, |d₂ k|))
        * (∑ i, |d₃ i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

    _ =
      B ^ 3 *
        ((∑ j, |d₁ j|)
          * (∑ k, |d₂ k|)
          * (∑ i, |d₃ i|)) := by
      ring

#print axioms abs_trace_V_diag_V_diag_V_diag_le

end

end RHFormalization
