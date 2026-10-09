import RHFormalization.PolylogWeightSummable
import Mathlib

/-!
# PolylogCenteredAbel — PL-4b-i: polylog partial sums ⟹ uniformly bounded shifted sums

If `‖Σ_{k≤m} b k‖ ≤ C·(log(m+1))^A` for all `m`, then for every `δ > 0`
`‖Σ_{k≤n} b k · (k+1)^{−δ}‖` is bounded uniformly in `n`.  Assembly of PL-1
(`abel_transfer_norm_bound_growing`) and PL-2 (`polylog_abel_weights_bounded`).
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

theorem centered_abel_uniform (b : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m : ℕ, ‖∑ k ∈ Finset.range (m+1), b k‖ ≤ C * (Real.log ((m:ℝ) + 1)) ^ A) :
    ∃ K : ℝ, ∀ n : ℕ,
      ‖∑ k ∈ Finset.range (n+1), b k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)‖ ≤ K := by
  obtain ⟨K0, hK0⟩ := polylog_abel_weights_bounded δ hδ A
  refine ⟨C * K0, fun n => ?_⟩
  have hab := abel_transfer_norm_bound_growing b
    (fun k => ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ))
    (fun m => C * (Real.log ((m:ℝ) + 1)) ^ A) hb n
  beta_reduce at hab
  have hw : ∀ k : ℕ, ‖((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)‖ = ((k:ℝ) + 1) ^ (-δ) := by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hdiff : ∀ k : ℕ,
      ‖((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) - (((((k+1:ℕ):ℝ) + 1) ^ (-δ) : ℝ) : ℂ)‖
        = ((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ) := by
    intro k
    have h2 : (((k+1:ℕ):ℝ) + 1) = (k:ℝ) + 2 := by push_cast; ring
    rw [h2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply abs_of_nonneg
    have := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < (k:ℝ) + 1)
      (by linarith : (k:ℝ) + 1 ≤ (k:ℝ) + 2) (by linarith : -δ ≤ 0)
    linarith
  rw [hw] at hab
  simp_rw [hdiff] at hab
  have hfactor :
      C * Real.log ((n:ℝ) + 1) ^ A * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n,
            C * Real.log ((k:ℝ) + 1) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
      = C * (Real.log ((n:ℝ) + 1) ^ A * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n,
            Real.log ((k:ℝ) + 1) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))) := by
    rw [mul_add, Finset.mul_sum]
    simp only [mul_assoc]
  calc _ ≤ _ := hab
    _ = _ := hfactor
    _ ≤ C * K0 := mul_le_mul_of_nonneg_left (hK0 n) hC

#print axioms centered_abel_uniform

end RHFormalization
