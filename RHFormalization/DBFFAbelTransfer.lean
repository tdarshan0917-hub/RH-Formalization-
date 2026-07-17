import RHFormalization.AbelSummableFromCumulative

/-!
# DBFFAbelTransfer — D.OP.2 engine (⟸ direction), abstract layer

ROUTE CARD
1. Target: the Abel mechanism of Lemma D.OP.2 — cumulative-error bound (★)
   transfers to boundedness of compensated weighted sums (B^can_α − M_α shape).
2. Objects: `abel_partial_sum` (banked donor, generalized to ℂ here).
3. Raw B on Ω? NO (abstract ℕ-indexed sums only).
4. R = F − raw B forced? NO. 5. True outright (pure Abel summation).
6. Manuscript: D.OP-BOUND, Lemma D.OP.2, ⟸ direction (the consumed one;
   ⟹ converse deferred — not load-bearing for the endpoint).
7. Consumer: next file instantiates e = vonMangoldt/main-term increments,
   w = stage kernel weights; K-uniform W, V from compact geometry.
-/

set_option autoImplicit false

namespace RHFormalization

open Finset

/-- Abel summation identity over ℂ (donor proof, coefficients complexified). -/
theorem abel_partial_sum_c (a w : ℕ → ℂ) (n : ℕ) :
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

/-- Real cumulative sums, complexified, keep their bound in norm. -/
theorem norm_cast_cumulative_le (e : ℕ → ℝ) (C : ℝ)
    (hE : ∀ n : ℕ, |∑ k ∈ range (n+1), e k| ≤ C) (m : ℕ) :
    ‖(∑ j ∈ range (m+1), ((e j : ℂ)))‖ ≤ C := by
  have hcast : (∑ j ∈ range (m+1), ((e j : ℂ)))
      = (((∑ j ∈ range (m+1), e j : ℝ)) : ℂ) := by
    first
      | (push_cast; ring)
      | (norm_cast)
      | (rw [Complex.ofReal_sum])
  rw [hcast]
  first
    | (rw [Complex.norm_real, Real.norm_eq_abs]; exact hE m)
    | (rw [Complex.norm_ofReal, Real.norm_eq_abs]; exact hE m)
    | (simpa [Real.norm_eq_abs] using hE m)

/-- **Abel transfer (finite form).** If the cumulative error is bounded by `C`,
every weighted partial sum is bounded by `C·(‖w n‖ + variation)`. -/
theorem abel_transfer_norm_bound
    (e : ℕ → ℝ) (w : ℕ → ℂ) (C : ℝ)
    (hE : ∀ n : ℕ, |∑ k ∈ range (n+1), e k| ≤ C) (n : ℕ) :
    ‖∑ k ∈ range (n+1), ((e k : ℂ)) * w k‖
      ≤ C * (‖w n‖ + ∑ k ∈ range n, ‖w k - w (k+1)‖) := by
  rw [abel_partial_sum_c (fun k => ((e k : ℂ))) w n]
  have hcum := norm_cast_cumulative_le e C hE
  calc ‖(∑ k ∈ range (n+1), ((e k : ℂ))) * w n
        + ∑ k ∈ range n, (∑ j ∈ range (k+1), ((e j : ℂ))) * (w k - w (k+1))‖
      ≤ ‖(∑ k ∈ range (n+1), ((e k : ℂ))) * w n‖
        + ‖∑ k ∈ range n, (∑ j ∈ range (k+1), ((e j : ℂ))) * (w k - w (k+1))‖ :=
        norm_add_le _ _
    _ ≤ C * ‖w n‖ + ∑ k ∈ range n, C * ‖w k - w (k+1)‖ := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hcum n) (norm_nonneg _)
        · refine le_trans (norm_sum_le _ _) ?_
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hcum k) (norm_nonneg _)
    _ = C * (‖w n‖ + ∑ k ∈ range n, ‖w k - w (k+1)‖) := by
        first
          | (rw [mul_add, Finset.mul_sum])
          | (rw [mul_add, Finset.mul_sum]; ring)
          | (simp only [mul_add, Finset.mul_sum])
          | (simp [mul_add, Finset.mul_sum]; done)

/-- **D.OP.2 engine (⟸, uniform form).** Bounded cumulative error (★-shape)
against weights with uniformly bounded norm and variation ⟹ the weighted
partial sums are uniformly bounded — the exact transfer that turns (★) into
`{B^can_α − M_α}` boundedness once instantiated. -/
theorem abel_transfer_uniform
    (e : ℕ → ℝ) (w : ℕ → ℂ) (C W V : ℝ)
    (hE : ∀ n : ℕ, |∑ k ∈ range (n+1), e k| ≤ C)
    (hW : ∀ n : ℕ, ‖w n‖ ≤ W)
    (hV : ∀ n : ℕ, (∑ k ∈ range n, ‖w k - w (k+1)‖) ≤ V) :
    ∀ n : ℕ, ‖∑ k ∈ range (n+1), ((e k : ℂ)) * w k‖ ≤ C * (W + V) := by
  intro n
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg _) (hE 0)
  refine le_trans (abel_transfer_norm_bound e w C hE n) ?_
  exact mul_le_mul_of_nonneg_left (add_le_add (hW n) (hV n)) hC0

#print axioms abel_partial_sum_c
#print axioms norm_cast_cumulative_le
#print axioms abel_transfer_norm_bound
#print axioms abel_transfer_uniform

end RHFormalization
