-- SENTINEL: MASSBOUND-v3
import RHFormalization.EigenvalueGrowthSummable
import RHFormalization.RemainderTraceZBound
import Mathlib

/-!
# FreeResolventMassBound — input 1 of 4 for the Z bound

CONSUMER: the `hmass` hypothesis of `norm_remainder_trace_le` (ZBOUND),
whose consumer is `hr` of `seam_bdd_of_parts` → `h_ctail_le_of_seam_bdd` → GATE.

    Σ_i ‖(s + λ_i)⁻¹‖ ≤ A · Σ'_n (1 + c(n+1)²)⁻¹,    A = 2(1+M+δ)/δ

with M ≥ ‖s‖, δ ≤ ‖s+λ_i‖, and Weyl growth c(i+1)² ≤ λ_i. The right side is a
CONVERGENT p-series (banked `summable_resolvent_of_weyl`) — N never appears.
This is the mechanism behind the measurement |Z| = 6.4976e-2 → 6.5024e-2, N=8→128.

Key inequality, no case split: A‖s+λ‖ ≥ max(2(1+M), 2(λ−M)) ≥ 1+λ.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- Termwise comparison: the resolvent modulus dominates `(1+λ)/A`. -/
theorem inv_norm_resolvent_le
    (s : ℂ) (lamv : ℝ) (hlam : 0 ≤ lamv) (M : ℝ) (hM : ‖s‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hlow : δ ≤ ‖s + (lamv : ℂ)‖) :
    ‖(s + (lamv : ℂ))⁻¹‖ ≤ (2 * (1 + M + δ) / δ) * (1 + lamv)⁻¹ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg s) hM
  have hpos : 0 < ‖s + (lamv : ℂ)‖ := lt_of_lt_of_le hδ hlow
  have h1pos : (0:ℝ) < 1 + lamv := by linarith
  have hnl : ‖(lamv : ℂ)‖ = lamv := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
  have hsub : ‖(lamv : ℂ)‖ ≤ ‖s + (lamv : ℂ)‖ + ‖s‖ := by
    have h := norm_sub_le (s + (lamv : ℂ)) s
    have heq : (s + (lamv : ℂ)) - s = (lamv : ℂ) := by ring
    rw [heq] at h
    exact h
  have hlow2 : lamv - M ≤ ‖s + (lamv : ℂ)‖ := by
    rw [hnl] at hsub
    linarith
  set A : ℝ := 2 * (1 + M + δ) / δ with hA
  have hA0 : (0:ℝ) < A := by rw [hA]; positivity
  have hAδ : A * δ = 2 * (1 + M + δ) := by
    rw [hA]; field_simp
  have hA2 : 2 ≤ A := by
    by_contra hcon
    push_neg at hcon
    have hlt : A * δ < 2 * δ := mul_lt_mul_of_pos_right hcon hδ
    rw [hAδ] at hlt
    linarith
  have hb1 : 2 * (1 + M + δ) ≤ A * ‖s + (lamv : ℂ)‖ := by
    have hstep : A * δ ≤ A * ‖s + (lamv : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hlow (le_of_lt hA0)
    rw [hAδ] at hstep
    exact hstep
  have hb2 : 2 * (lamv - M) ≤ A * ‖s + (lamv : ℂ)‖ := by
    rcases le_total 0 (lamv - M) with hge | hle
    · have h1 : A * (lamv - M) ≤ A * ‖s + (lamv : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hlow2 (le_of_lt hA0)
      have h2 : 2 * (lamv - M) ≤ A * (lamv - M) :=
        mul_le_mul_of_nonneg_right hA2 hge
      linarith
    · have hpos2 : 0 < A * ‖s + (lamv : ℂ)‖ := mul_pos hA0 hpos
      linarith
  have key : (1 + lamv) ≤ A * ‖s + (lamv : ℂ)‖ := by linarith
  have hinv := inv_anti₀ h1pos key
  rw [mul_inv] at hinv
  have hmul := mul_le_mul_of_nonneg_left hinv (le_of_lt hA0)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hA0), one_mul] at hmul
  rw [norm_inv]
  exact hmul

/-- **Input 1 of 4: the N-free free-resolvent mass bound.** -/
theorem free_resolvent_mass_le
    {N : ℕ} (lam : Fin N → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (s : ℂ) (M : ℝ) (hM : ‖s‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ i, δ ≤ ‖s + (lam i : ℂ)‖)
    {c : ℝ} (hc : 0 < c)
    (hgrow : ∀ i : Fin N, c * (((i : ℕ) : ℝ) + 1) ^ 2 ≤ lam i) :
    ∑ i, ‖(s + (lam i : ℂ))⁻¹‖
      ≤ (2 * (1 + M + δ) / δ) * ∑' n : ℕ, (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg s) hM
  set A : ℝ := 2 * (1 + M + δ) / δ with hA
  have hA0 : (0:ℝ) ≤ A := by rw [hA]; positivity
  set g : ℕ → ℝ := fun n => (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹ with hg
  have hgnn : ∀ n : ℕ, 0 ≤ g n := by
    intro n; rw [hg]; positivity
  have hsum : Summable g := by
    have hbase := summable_resolvent_of_weyl
      (fun n : ℕ => c * (((n : ℕ) : ℝ) + 1) ^ 2)
      (fun n => by positivity) c 0 hc
      (by
        intro n
        have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hsq : ((n : ℝ)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hsq hc.le
        simp only []
        linarith)
    simpa [hg] using hbase
  have hterm : ∀ i : Fin N, ‖(s + (lam i : ℂ))⁻¹‖ ≤ A * g i := by
    intro i
    have h1 := inv_norm_resolvent_le s (lam i) (hlam i) M hM hδ (hlow i)
    refine le_trans h1 ?_
    have hle : (1 + c * (((i : ℕ) : ℝ) + 1) ^ 2) ≤ 1 + lam i := by
      have := hgrow i; linarith
    have hp1 : (0:ℝ) < 1 + c * (((i : ℕ) : ℝ) + 1) ^ 2 := by positivity
    have hinv : (1 + lam i)⁻¹ ≤ g i := by
      rw [hg]
      exact inv_anti₀ hp1 hle
    exact mul_le_mul_of_nonneg_left hinv hA0
  calc ∑ i, ‖(s + (lam i : ℂ))⁻¹‖
      ≤ ∑ i : Fin N, A * g i := Finset.sum_le_sum (fun i _ => hterm i)
    _ = A * ∑ i : Fin N, g (i : ℕ) := by rw [Finset.mul_sum]
    _ = A * ∑ n ∈ Finset.range N, g n := by
        rw [Fin.sum_univ_eq_sum_range (fun n => g n) N]
    _ ≤ A * ∑' n : ℕ, g n := by
        refine mul_le_mul_of_nonneg_left ?_ hA0
        exact hsum.sum_le_tsum (Finset.range N) (fun n _ => hgnn n)

#print axioms inv_norm_resolvent_le
#print axioms free_resolvent_mass_le

end

end RHFormalization
