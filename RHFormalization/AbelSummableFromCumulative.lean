import Mathlib

/-!
# Abel brick (abstract): summability of a·w from a cumulative envelope

If a ≥ 0, w ≥ 0 decreasing, the partial sums Aₙ = Σ_{k≤n} aₖ satisfy Aₙ ≤ Fₙ,
Fₙwₙ ≤ B₀ uniformly, and Fₖ(wₖ−wₖ₊₁) is dominated by a summable g, then Σ aₖwₖ
converges. Pure Abel summation; the concrete zero-count instantiation
(F = C·n·log n envelope from `cumulativeBand_loglinear`, w = 1/(1+k²)) follows
in the companion file.
-/

namespace RHFormalization
open Finset

/-- Abel summation identity for partial sums against a weight. -/
theorem abel_partial_sum (a w : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n+1), a k * w k
      = (∑ k ∈ range (n+1), a k) * w n
        + ∑ k ∈ range n, (∑ j ∈ range (k+1), a j) * (w k - w (k+1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h1 : ∑ k ∈ range (m+2), a k * w k
          = (∑ k ∈ range (m+1), a k * w k) + a (m+1) * w (m+1) :=
        sum_range_succ _ _
      have h2 : ∑ k ∈ range (m+1), (∑ j ∈ range (k+1), a j) * (w k - w (k+1))
          = (∑ k ∈ range m, (∑ j ∈ range (k+1), a j) * (w k - w (k+1)))
            + (∑ j ∈ range (m+1), a j) * (w m - w (m+1)) :=
        sum_range_succ _ _
      have h3 : ∑ k ∈ range (m+2), a k
          = (∑ k ∈ range (m+1), a k) + a (m+1) :=
        sum_range_succ _ _
      rw [h1, ih, h2, h3]
      ring

/-- **Abstract Abel brick.** Cumulative envelope + decreasing weights ⟹ summable. -/
theorem summable_mul_weight_of_cumulative_bound
    (a w F : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k)
    (hw_nonneg : ∀ k, 0 ≤ w k)
    (hw_anti : ∀ k, w (k+1) ≤ w k)
    (hAF : ∀ n, (∑ k ∈ range (n+1), a k) ≤ F n)
    (B0 : ℝ) (hFw : ∀ n, F n * w n ≤ B0)
    (g : ℕ → ℝ) (hg_nonneg : ∀ k, 0 ≤ g k) (hg_sum : Summable g)
    (hg : ∀ k, F k * (w k - w (k+1)) ≤ g k) :
    Summable (fun k => a k * w k) := by
  -- the uniform cap
  have hF0 : (0:ℝ) ≤ F 0 := le_trans (by simpa using ha 0) (by simpa using hAF 0)
  have hB0 : (0:ℝ) ≤ B0 := le_trans (mul_nonneg hF0 (hw_nonneg 0)) (hFw 0)
  have htsum_nonneg : (0:ℝ) ≤ ∑' k, g k := tsum_nonneg hg_nonneg
  apply summable_of_sum_range_le
    (c := B0 + ∑' k, g k)
    (fun k => mul_nonneg (ha k) (hw_nonneg k))
  intro n
  cases n with
  | zero => simpa using add_nonneg hB0 htsum_nonneg
  | succ m =>
      rw [abel_partial_sum a w m]
      have hstep1 : (∑ k ∈ range (m+1), a k) * w m ≤ F m * w m :=
        mul_le_mul_of_nonneg_right (hAF m) (hw_nonneg m)
      have hstep2 :
          ∑ k ∈ range m, (∑ j ∈ range (k+1), a j) * (w k - w (k+1))
            ≤ ∑ k ∈ range m, g k := by
        apply Finset.sum_le_sum
        intro k _
        have hΔ : (0:ℝ) ≤ w k - w (k+1) := sub_nonneg.mpr (hw_anti k)
        calc (∑ j ∈ range (k+1), a j) * (w k - w (k+1))
            ≤ F k * (w k - w (k+1)) :=
              mul_le_mul_of_nonneg_right (hAF k) hΔ
          _ ≤ g k := hg k
      have hstep3 : ∑ k ∈ range m, g k ≤ ∑' k, g k :=
        hg_sum.sum_le_tsum (range m) (fun k _ => hg_nonneg k)
      calc (∑ k ∈ range (m+1), a k) * w m
              + ∑ k ∈ range m, (∑ j ∈ range (k+1), a j) * (w k - w (k+1))
            ≤ F m * w m + ∑ k ∈ range m, g k := add_le_add hstep1 hstep2
        _ ≤ B0 + ∑' k, g k := add_le_add (hFw m) hstep3

#print axioms abel_partial_sum
#print axioms summable_mul_weight_of_cumulative_bound

end RHFormalization
