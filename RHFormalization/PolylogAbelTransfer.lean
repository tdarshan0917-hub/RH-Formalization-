import RHFormalization.DBFFAbelTransfer
import Mathlib

/-!
# PolylogAbelTransfer — PL-1: Abel transfer with a growing partial-sum bound

* `abel_transfer_norm_bound_growing`: if `‖Σ_{k≤m} a k‖ ≤ e m` for all `m`, then
  `‖Σ_{k≤n} a k * w k‖ ≤ e n * ‖w n‖ + Σ_{k<n} e k * ‖w k − w (k+1)‖`.
* `rpow_neg_sub_rpow_neg_le`: `(x+1)^{-δ} − (x+2)^{-δ} ≤ δ · (x+1)^{-δ} / (x+1)`.
First brick of the polylog upgrade of the Stage A endpoint.
-/

set_option autoImplicit false

namespace RHFormalization

open Finset
open scoped BigOperators

theorem abel_transfer_norm_bound_growing
    (a w : ℕ → ℂ) (e : ℕ → ℝ)
    (hA : ∀ m : ℕ, ‖∑ k ∈ range (m+1), a k‖ ≤ e m)
    (n : ℕ) :
    ‖∑ k ∈ range (n+1), a k * w k‖
      ≤ e n * ‖w n‖ + ∑ k ∈ range n, e k * ‖w k - w (k+1)‖ := by
  rw [abel_partial_sum_c a w n]
  calc
    ‖(∑ k ∈ range (n+1), a k) * w n
        + ∑ k ∈ range n, (∑ j ∈ range (k+1), a j) * (w k - w (k+1))‖
        ≤ ‖(∑ k ∈ range (n+1), a k) * w n‖
          + ‖∑ k ∈ range n, (∑ j ∈ range (k+1), a j) * (w k - w (k+1))‖ :=
            norm_add_le _ _
    _ ≤ e n * ‖w n‖ + ∑ k ∈ range n, e k * ‖w k - w (k+1)‖ := by
        gcongr
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _)
        · calc ‖∑ k ∈ range n, (∑ j ∈ range (k+1), a j) * (w k - w (k+1))‖
              ≤ ∑ k ∈ range n, ‖(∑ j ∈ range (k+1), a j) * (w k - w (k+1))‖ :=
                norm_sum_le _ _
            _ ≤ ∑ k ∈ range n, e k * ‖w k - w (k+1)‖ := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _)

theorem one_sub_rpow_neg_le {u δ : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) :
    1 - (1 + u) ^ (-δ) ≤ δ * u := by
  have h1u : 0 < 1 + u := by linarith
  have hlog : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1u
    linarith
  have hexp : 1 + (-(δ * Real.log (1 + u))) ≤ Real.exp (-(δ * Real.log (1 + u))) := by
    have := Real.add_one_le_exp (-(δ * Real.log (1 + u)))
    linarith
  have hrpow : (1 + u) ^ (-δ) = Real.exp (Real.log (1 + u) * (-δ)) :=
    Real.rpow_def_of_pos h1u _
  rw [hrpow]
  have hmul : δ * Real.log (1 + u) ≤ δ * u := mul_le_mul_of_nonneg_left hlog hδ
  have : Real.log (1 + u) * (-δ) = -(δ * Real.log (1 + u)) := by ring
  rw [this]
  linarith

theorem rpow_neg_sub_rpow_neg_le {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    (x + 1) ^ (-δ) - (x + 2) ^ (-δ) ≤ δ * (x + 1) ^ (-δ) / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hsplit : x + 2 = (x + 1) * (1 + 1 / (x + 1)) := by
    field_simp
    ring
  have hpos1 : 0 < 1 + 1 / (x + 1) := by positivity
  have hprod : (x + 2) ^ (-δ) = (x + 1) ^ (-δ) * (1 + 1 / (x + 1)) ^ (-δ) := by
    rw [hsplit, Real.mul_rpow hx1.le hpos1.le]
  rw [hprod]
  have hw0 : 0 ≤ (x + 1) ^ (-δ) := Real.rpow_nonneg hx1.le _
  have hb := one_sub_rpow_neg_le (u := 1 / (x + 1)) (by positivity) hδ
  calc (x + 1) ^ (-δ) - (x + 1) ^ (-δ) * (1 + 1 / (x + 1)) ^ (-δ)
      = (x + 1) ^ (-δ) * (1 - (1 + 1 / (x + 1)) ^ (-δ)) := by ring
    _ ≤ (x + 1) ^ (-δ) * (δ * (1 / (x + 1))) := mul_le_mul_of_nonneg_left hb hw0
    _ = δ * (x + 1) ^ (-δ) / (x + 1) := by ring

#print axioms abel_transfer_norm_bound_growing
#print axioms rpow_neg_sub_rpow_neg_le

end RHFormalization
