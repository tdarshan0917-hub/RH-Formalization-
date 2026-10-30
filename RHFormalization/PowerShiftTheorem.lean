import RHFormalization.PolylogShiftTheorem
import RHFormalization.PolylogWeightSummable
import Mathlib

/-!
# PowerShiftTheorem — PE-1: power growth `M^ε` at ρ ⟹ bounded discrepancy at ρ + δ

Power analogue of PL-5a. For `ε ≤ δ/2`, the Abel weights absorb growth `(k+1)^ε`:
`(n+1)^ε (n+1)^{−δ} + Σ_{k<n} (k+1)^ε ((k+1)^{−δ} − (k+2)^{−δ}) ≤ K(δ, ε)`.
Hence `‖vmDiscrepancy (m+1) ρ‖ ≤ C (m+1)^ε` for all `m` gives
`‖vmDiscrepancy M (ρ+δ)‖ ≤ K` for all `M ≥ 1`, uniformly in `ρ`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- **PE-1a**: the Abel weights absorb power growth `(k+1)^ε` when `ε ≤ δ/2`. -/
theorem power_abel_weights_bounded (δ ε : ℝ) (hδ : 0 < δ) (hε : ε ≤ δ / 2) :
    ∃ K : ℝ, ∀ n : ℕ,
      ((n:ℝ) + 1) ^ ε * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n,
            ((k:ℝ) + 1) ^ ε * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
      ≤ K := by
  have hbdry : ∀ n : ℕ, ((n:ℝ) + 1) ^ ε * ((n:ℝ) + 1) ^ (-δ) ≤ 1 := by
    intro n
    have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    rw [← Real.rpow_add (by linarith : (0:ℝ) < (n:ℝ) + 1)]
    have h := Real.rpow_le_rpow_of_exponent_le hn1 (show ε + -δ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hterm : ∀ k : ℕ,
      ((k:ℝ) + 1) ^ ε * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
        ≤ δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) := by
    intro k
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by linarith
    have hk1' : (1:ℝ) ≤ (k:ℝ) + 1 := by linarith
    have hp : ((k:ℝ) + 1) ^ ε ≤ ((k:ℝ) + 1) ^ (δ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hk1' hε
    have hd := rpow_neg_sub_rpow_neg_le (x := (k:ℝ)) hk0 hδ.le
    have hd0 : 0 ≤ ((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ) := by
      have hmono : ((k:ℝ) + 2) ^ (-δ) ≤ ((k:ℝ) + 1) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hk1 (by linarith) (by linarith)
      linarith
    calc ((k:ℝ) + 1) ^ ε * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
        ≤ ((k:ℝ) + 1) ^ (δ / 2) * (δ * ((k:ℝ) + 1) ^ (-δ) / ((k:ℝ) + 1)) :=
          mul_le_mul hp hd hd0 (by positivity)
      _ = δ * (((k:ℝ) + 1) ^ (δ / 2) * ((k:ℝ) + 1) ^ (-δ) / ((k:ℝ) + 1)) := by ring
      _ = δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) := by
          congr 1
          rw [← Real.rpow_add hk1, ← Real.rpow_sub_one hk1.ne']
          congr 1
          ring
  have hsum := summable_shifted_rpow δ hδ δ
  have hg0 : ∀ k : ℕ, 0 ≤ δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) :=
    fun k => mul_nonneg hδ.le (Real.rpow_nonneg (by positivity) _)
  refine ⟨1 + ∑' k : ℕ, δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)), fun n => ?_⟩
  have hpartial : ∑ k ∈ Finset.range n,
      ((k:ℝ) + 1) ^ ε * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
        ≤ ∑' k : ℕ, δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) := by
    calc _ ≤ ∑ k ∈ Finset.range n, δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ ≤ ∑' k : ℕ, δ * ((k:ℝ) + 1) ^ (-(1 + δ / 2)) :=
          hsum.sum_le_tsum _ (fun k _ => hg0 k)
  linarith [hbdry n, hpartial]

/-- Abel bound with an arbitrary growth profile `g` (generalizes PL-4b-i). -/
theorem centered_abel_bound_gen (b : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (g : ℕ → ℝ) {C K0 : ℝ}
    (hC : 0 ≤ C)
    (hK0 : ∀ n : ℕ,
      g n * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n, g k * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
      ≤ K0)
    (hb : ∀ m : ℕ, ‖∑ k ∈ Finset.range (m+1), b k‖ ≤ C * g m)
    (n : ℕ) :
    ‖∑ k ∈ Finset.range (n+1), b k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)‖ ≤ C * K0 := by
  have hab := abel_transfer_norm_bound_growing b
    (fun k => ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ))
    (fun m => C * g m) hb n
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
      C * g n * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n, C * g k * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
      = C * (g n * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n, g k * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))) := by
    rw [mul_add, Finset.mul_sum]
    simp only [mul_assoc]
  calc _ ≤ _ := hab
    _ = _ := hfactor
    _ ≤ C * K0 := mul_le_mul_of_nonneg_left (hK0 n) hC

/-- **PE-1**: power growth `(m+1)^ε` at ρ ⟹ bounded discrepancy at ρ + δ (`ε ≤ δ/2`),
uniformly in ρ. -/
theorem shifted_vmDiscrepancy_uniform_pow {δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ / 2)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ≠ 1 → ρ + (δ:ℂ) ≠ 1 →
      (∀ m : ℕ, ‖vmDiscrepancy (m + 1) ρ‖ ≤ C * ((m:ℝ) + 1) ^ ε) →
      ∀ M : ℕ, 1 ≤ M → ‖vmDiscrepancy M (ρ + (δ:ℂ))‖ ≤ K := by
  obtain ⟨K0, hK0⟩ := power_abel_weights_bounded δ ε hδ hε
  refine ⟨C * K0 + 1, fun ρ hre hρ hρδ hD M hM => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have hb : ∀ m : ℕ, ‖∑ k ∈ Finset.range (m + 1), centeredVM ρ k‖
      ≤ C * ((m:ℝ) + 1) ^ ε := by
    intro m
    rw [centeredVM_partialSum]
    exact hD m
  have habel := centered_abel_bound_gen (centeredVM ρ) hδ.le
    (fun m : ℕ => ((m:ℝ) + 1) ^ ε) hC hK0 hb N
  have hE := mainIncr_shift_sum_le (le_refl (0:ℝ)) hre hδ.le hρ hρδ (N + 1)
  rw [vmDiscrepancy_shift_eq ρ δ hM]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ C * K0 + 1 := add_le_add habel hE

#print axioms power_abel_weights_bounded
#print axioms centered_abel_bound_gen
#print axioms shifted_vmDiscrepancy_uniform_pow

end

end RHFormalization
