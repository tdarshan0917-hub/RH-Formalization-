import RHFormalization.GalerkinDuhamelTrace
import RHFormalization.VMatrixElementBound

/-!
# Brick 2, stone 6: bound on the Duhamel trace term
`|Tr(V·diag(d₁)·V·diag(d₂))| ≤ B²·(∑|d₁|)(∑|d₂|)` when `|V_{mn}| ≤ B`. With
heat-kernel weights this is the quantitative trace-norm bound. Off-diagonal decay
NOT used — boundedness + heat decay suffice.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **Stone 6 (abstract)**: trace bound from entrywise bound `|V_{mn}| ≤ B`. -/
theorem abs_trace_V_diag_V_diag_le
    (V : Matrix (Fin N) (Fin N) ℝ) (d₁ d₂ : Fin N → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hV : ∀ i j, |V i j| ≤ B) :
    |(V * Matrix.diagonal d₁ * V * Matrix.diagonal d₂).trace|
      ≤ B ^ 2 * ((∑ n, |d₁ n|) * (∑ m, |d₂ m|)) := by
  rw [trace_V_diag_V_diag]
  calc |∑ m, ∑ n, V m n * d₁ n * V n m * d₂ m|
      ≤ ∑ m, |∑ n, V m n * d₁ n * V n m * d₂ m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, ∑ n, |V m n * d₁ n * V n m * d₂ m| := by
        apply Finset.sum_le_sum; intro m _; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, ∑ n, B ^ 2 * (|d₁ n| * |d₂ m|) := by
        apply Finset.sum_le_sum; intro m _
        apply Finset.sum_le_sum; intro n _
        rw [abs_mul, abs_mul, abs_mul]
        have hbound : |V m n| * |d₁ n| * |V n m| * |d₂ m| ≤ B * |d₁ n| * B * |d₂ m| := by
          gcongr
          · exact hV m n
          · exact hV n m
        calc |V m n| * |d₁ n| * |V n m| * |d₂ m|
            ≤ B * |d₁ n| * B * |d₂ m| := hbound
          _ = B ^ 2 * (|d₁ n| * |d₂ m|) := by ring
    _ = B ^ 2 * ((∑ n, |d₁ n|) * (∑ m, |d₂ m|)) := by
        have hfactor : (∑ m, ∑ n, B ^ 2 * (|d₁ n| * |d₂ m|))
            = ∑ m, (B ^ 2 * |d₂ m|) * ∑ n, |d₁ n| := by
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n _
          ring
        rw [hfactor, ← Finset.sum_mul]
        rw [show (∑ m, B ^ 2 * |d₂ m|) = B ^ 2 * ∑ m, |d₂ m| from by
          rw [Finset.mul_sum]]
        ring

/-- **Stone 6 (Galerkin)**: Duhamel trace of the genuine `V = galerkinV` bounded
by `B²·(∑|d₁|)(∑|d₂|)`, `B = ∑_q |w(q)|·bumpMass(q)`. -/
theorem abs_trace_galerkinV_diag_le
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (d₁ d₂ : Fin N → ℝ) :
    |(galerkinV δ qs w L * Matrix.diagonal d₁ * galerkinV δ qs w L
        * Matrix.diagonal d₂).trace|
      ≤ ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
          * ((∑ n, |d₁ n|) * (∑ m, |d₂ m|)) := by
  have hBnn : 0 ≤ ∑ q ∈ qs, |w q| * bumpMass δ q L := by
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg (abs_nonneg _)
    unfold bumpMass
    apply intervalIntegral.integral_nonneg hL
    intro x _
    exact le_of_lt (gaussBump_pos δ hδ _)
  have h2L : (0 : ℝ) ≤ 2 / L := by positivity
  apply abs_trace_V_diag_V_diag_le
  · exact mul_nonneg h2L hBnn
  · intro i j
    rw [galerkinV_apply, abs_mul]
    have habs2L : |2 / L| = 2 / L := abs_of_nonneg h2L
    rw [habs2L]
    exact mul_le_mul_of_nonneg_left
      (abs_VmatrixElement_le δ hδ qs w L hL (i + 1) (j + 1)) h2L

#print axioms abs_trace_V_diag_V_diag_le
#print axioms abs_trace_galerkinV_diag_le
end
end RHFormalization
