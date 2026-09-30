import RHFormalization.DenseTwoModeCos
import Mathlib

/-!
# DensePairBlocks — KB3b-ii/iii: disjoint pair blocks and the pointwise pair bound

* `sum_range_two_blocks`: `Σ_{j<2mJ} f j = Σ_{b<J} Σ_{i<m} (f(2mb+i) + f(2mb+i+m))` —
  the indices `2mb+i` and `2mb+i+m` are disjoint across all `(b,i)`, so summing over
  pairs is a sub-sum of the full diagonal sum with no double counting.
* `pair_sq_ge_of_phase`: if `x`, `y` are within `K` of `cos θ·D`, `cos(θ+π/2+η)·D`,
  then `x² + y² ≥ (1 − 2|η|)·D²/2 − 2K²`.
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

theorem sum_range_add' (f : ℕ → ℝ) (n m : ℕ) :
    ∑ x ∈ Finset.range (n + m), f x
      = ∑ x ∈ Finset.range n, f x + ∑ x ∈ Finset.range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by ring, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem sum_range_two_blocks (f : ℕ → ℝ) (m J : ℕ) :
    ∑ j ∈ Finset.range (2 * m * J), f j
      = ∑ b ∈ Finset.range J, ∑ i ∈ Finset.range m,
          (f (2 * m * b + i) + f (2 * m * b + i + m)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [show 2 * m * (J + 1) = 2 * m * J + 2 * m by ring, sum_range_add', ih,
      Finset.sum_range_succ]
    congr 1
    have h2 : ∑ x ∈ Finset.range (2 * m), f (2 * m * J + x)
        = ∑ x ∈ Finset.range m, f (2 * m * J + x)
          + ∑ x ∈ Finset.range m, f (2 * m * J + (m + x)) := by
      rw [show 2 * m = m + m by ring]
      exact sum_range_add' _ m m
    rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show 2 * m * J + (m + i) = 2 * m * J + i + m by ring]

theorem sum_range_prefix_le (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) {P N : ℕ} (h : P ≤ N) :
    ∑ j ∈ Finset.range P, f j ≤ ∑ j ∈ Finset.range N, f j :=
  by
    have hsub : Finset.range P ⊆ Finset.range N := fun j hj =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) h)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intros
    exact hf _

/-- **KB3b-iii**: the pointwise pair bound. -/
theorem pair_sq_ge_of_phase (x y D K θ η : ℝ)
    (hx : |x - Real.cos θ * D| ≤ K)
    (hy : |y - Real.cos (θ + Real.pi / 2 + η) * D| ≤ K) :
    x ^ 2 + y ^ 2 ≥ (1 - 2 * |η|) * D ^ 2 / 2 - 2 * K ^ 2 := by
  have hx2 : (x - Real.cos θ * D) ^ 2 ≤ K ^ 2 := by
    have h := abs_le.mp hx; nlinarith [h.1, h.2]
  have hy2 : (y - Real.cos (θ + Real.pi / 2 + η) * D) ^ 2 ≤ K ^ 2 := by
    have h := abs_le.mp hy; nlinarith [h.1, h.2]
  have h1 : (Real.cos θ * D) ^ 2 ≤ 2 * x ^ 2 + 2 * (x - Real.cos θ * D) ^ 2 := by
    nlinarith [sq_nonneg (2 * x - Real.cos θ * D)]
  have h2 : (Real.cos (θ + Real.pi / 2 + η) * D) ^ 2
      ≤ 2 * y ^ 2 + 2 * (y - Real.cos (θ + Real.pi / 2 + η) * D) ^ 2 := by
    nlinarith [sq_nonneg (2 * y - Real.cos (θ + Real.pi / 2 + η) * D)]
  have hcos := cos_sq_add_cos_sq_quarter_ge θ η
  have hc : (Real.cos θ * D) ^ 2 + (Real.cos (θ + Real.pi / 2 + η) * D) ^ 2
      ≥ (1 - 2 * |η|) * D ^ 2 := by
    have := mul_le_mul_of_nonneg_right hcos (sq_nonneg D)
    calc (Real.cos θ * D) ^ 2 + (Real.cos (θ + Real.pi / 2 + η) * D) ^ 2
        = (Real.cos θ ^ 2 + Real.cos (θ + Real.pi / 2 + η) ^ 2) * D ^ 2 := by ring
      _ ≥ (1 - 2 * |η|) * D ^ 2 := this
  linarith [hx2, hy2, h1, h2, hc]

#print axioms sum_range_two_blocks
#print axioms pair_sq_ge_of_phase

end RHFormalization
