import RHFormalization.PolylogAbelTransfer
import Mathlib

/-!
# PolylogWeightSummable — PL-2: the Abel weights absorb any polylog growth

For `δ > 0` and `A : ℕ`, with `e k = (log(k+1))^A` and `w k = (k+1)^{-δ}`:
`e n * w n + Σ_{k<n} e k * (w k − w (k+1)) ≤ K(δ, A)` uniformly in `n`.
Key input: `log x ≤ x^ε / ε`, so `(log(k+1))^A ≤ (k+1)^{δ/2} / ε^A`.
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

/-- `(log(k+1))^A ≤ (k+1)^{δ/2} / ε^A` with `ε = δ / (2(A+1))`. -/
theorem log_pow_le_rpow_half (δ : ℝ) (hδ : 0 < δ) (A : ℕ) (k : ℕ) :
    (Real.log ((k:ℝ) + 1)) ^ A
      ≤ ((k:ℝ) + 1) ^ (δ / 2) / (δ / (2 * ((A:ℝ) + 1))) ^ A := by
  set ε : ℝ := δ / (2 * ((A:ℝ) + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hk1 : (1:ℝ) ≤ (k:ℝ) + 1 := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hlog0 : 0 ≤ Real.log ((k:ℝ) + 1) := Real.log_nonneg hk1
  have h1 : Real.log ((k:ℝ) + 1) ≤ ((k:ℝ) + 1) ^ ε / ε :=
    Real.log_le_rpow_div (by linarith) hεpos
  have h2 : (Real.log ((k:ℝ) + 1)) ^ A ≤ (((k:ℝ) + 1) ^ ε / ε) ^ A := by
    first
      | exact pow_le_pow_left₀ hlog0 h1 A
      | exact pow_le_pow_left hlog0 h1 A
      | gcongr
  have h3 : (((k:ℝ) + 1) ^ ε / ε) ^ A = ((k:ℝ) + 1) ^ (ε * (A:ℝ)) / ε ^ A := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  have hexp : ε * (A:ℝ) ≤ δ / 2 := by
    rw [hε]
    have hA0 : (0:ℝ) ≤ (A:ℝ) := Nat.cast_nonneg A
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : ((k:ℝ) + 1) ^ (ε * (A:ℝ)) ≤ ((k:ℝ) + 1) ^ (δ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hk1 hexp
  calc (Real.log ((k:ℝ) + 1)) ^ A
      ≤ (((k:ℝ) + 1) ^ ε / ε) ^ A := h2
    _ = ((k:ℝ) + 1) ^ (ε * (A:ℝ)) / ε ^ A := h3
    _ ≤ ((k:ℝ) + 1) ^ (δ / 2) / ε ^ A := by
        exact div_le_div_of_nonneg_right h4 (pow_nonneg hεpos.le A)

/-- The per-term majorant `g k = c · (k+1)^{-(1+δ/2)}` is summable. -/
theorem summable_shifted_rpow (δ : ℝ) (hδ : 0 < δ) (c : ℝ) :
    Summable (fun k : ℕ => c * ((k:ℝ) + 1) ^ (-(1 + δ / 2))) := by
  have h : Summable (fun n : ℕ => ((n:ℝ) ^ (1 + δ / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have h' : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (1 + δ / 2))⁻¹) :=
    (summable_nat_add_iff 1).mpr h
  refine (h'.mul_left c).congr (fun k => ?_)
  push_cast
  rw [Real.rpow_neg (by positivity)]

/-- **PL-2**: uniform bound for the Abel weight sum with polylog growth. -/
theorem polylog_abel_weights_bounded (δ : ℝ) (hδ : 0 < δ) (A : ℕ) :
    ∃ K : ℝ, ∀ n : ℕ,
      (Real.log ((n:ℝ) + 1)) ^ A * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n,
            (Real.log ((k:ℝ) + 1)) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
      ≤ K := by
  set ε : ℝ := δ / (2 * ((A:ℝ) + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  set c : ℝ := δ / ε ^ A with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  -- boundary term ≤ 1/ε^A
  have hbdry : ∀ n : ℕ,
      (Real.log ((n:ℝ) + 1)) ^ A * ((n:ℝ) + 1) ^ (-δ) ≤ 1 / ε ^ A := by
    intro n
    have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hl := log_pow_le_rpow_half δ hδ A n
    rw [← hε] at hl
    have hw0 : 0 ≤ ((n:ℝ) + 1) ^ (-δ) := Real.rpow_nonneg (by linarith) _
    calc (Real.log ((n:ℝ) + 1)) ^ A * ((n:ℝ) + 1) ^ (-δ)
        ≤ (((n:ℝ) + 1) ^ (δ / 2) / ε ^ A) * ((n:ℝ) + 1) ^ (-δ) :=
          mul_le_mul_of_nonneg_right hl hw0
      _ = ((n:ℝ) + 1) ^ (δ / 2 + -δ) / ε ^ A := by
          rw [Real.rpow_add (by linarith)]; ring
      _ ≤ 1 / ε ^ A := by
          have : ((n:ℝ) + 1) ^ (δ / 2 + -δ) ≤ 1 := by
            have h := Real.rpow_le_rpow_of_exponent_le hn1 (show δ / 2 + -δ ≤ 0 by linarith)
            rwa [Real.rpow_zero] at h
          exact div_le_div_of_nonneg_right this (pow_nonneg hεpos.le A)
  -- series term ≤ c · (k+1)^{-(1+δ/2)}
  have hterm : ∀ k : ℕ,
      (Real.log ((k:ℝ) + 1)) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
        ≤ c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) := by
    intro k
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by linarith
    have hl := log_pow_le_rpow_half δ hδ A k
    rw [← hε] at hl
    have hd := rpow_neg_sub_rpow_neg_le (x := (k:ℝ)) hk0 hδ.le
    have hd0 : 0 ≤ ((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ) := by
      have hmono : ((k:ℝ) + 2) ^ (-δ) ≤ ((k:ℝ) + 1) ^ (-δ) := by
        first
          | exact Real.rpow_le_rpow_of_nonpos hk1 (by linarith) (by linarith)
          | exact Real.rpow_le_rpow_of_exponent_nonpos hk1 (by linarith) (by linarith)
          | (rw [Real.rpow_neg hk1.le, Real.rpow_neg (by linarith)]
             exact inv_anti₀ (Real.rpow_pos_of_pos hk1 _)
               (Real.rpow_le_rpow hk1.le (by linarith) hδ.le))
      linarith
    have hlog0 : 0 ≤ (Real.log ((k:ℝ) + 1)) ^ A :=
      pow_nonneg (Real.log_nonneg (by linarith)) A
    calc (Real.log ((k:ℝ) + 1)) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
        ≤ (((k:ℝ) + 1) ^ (δ / 2) / ε ^ A) * (δ * ((k:ℝ) + 1) ^ (-δ) / ((k:ℝ) + 1)) :=
          mul_le_mul hl hd hd0 (by positivity)
      _ = c * (((k:ℝ) + 1) ^ (δ / 2) * ((k:ℝ) + 1) ^ (-δ) / ((k:ℝ) + 1)) := by
          rw [hc]; ring
      _ = c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) := by
          congr 1
          rw [← Real.rpow_add hk1, ← Real.rpow_sub_one hk1.ne']
          congr 1
          ring
  have hsum := summable_shifted_rpow δ hδ c
  have hg0 : ∀ k : ℕ, 0 ≤ c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) :=
    fun k => mul_nonneg hc0 (Real.rpow_nonneg (by positivity) _)
  refine ⟨1 / ε ^ A + ∑' k : ℕ, c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)), fun n => ?_⟩
  have hpartial : ∑ k ∈ Finset.range n,
      (Real.log ((k:ℝ) + 1)) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
        ≤ ∑' k : ℕ, c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) := by
    calc _ ≤ ∑ k ∈ Finset.range n, c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ ≤ ∑' k : ℕ, c * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) :=
          hsum.sum_le_tsum _ (fun k _ => hg0 k)
  linarith [hbdry n, hpartial]

#print axioms polylog_abel_weights_bounded

end RHFormalization
