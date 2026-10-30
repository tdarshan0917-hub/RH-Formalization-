import RHFormalization.PolylogShiftTheorem
import RHFormalization.PolylogWeightSummable
import Mathlib

/-!
# ZetaDiscrepancyBound — CV-1: the power-sum discrepancy is bounded for Re ρ > 0

`zetaDiscrepancy M ρ := Σ_{0<k≤M} k^{−ρ} − (M^{1−ρ} − 1)/(1−ρ)` is bounded, uniformly in
`M ≥ 1`, on `{c ≤ Re ρ, ‖ρ‖ ≤ R, ρ ≠ 1}` for any `c > 0`. Per term,
`k^{−ρ} − ∫_k^{k+1} x^{−ρ} dx = ∫_k^{k+1} (k^{−ρ} − x^{−ρ}) dx` and
`‖x^{−ρ} − k^{−ρ}‖ = ‖ρ ∫_k^x t^{−ρ−1} dt‖ ≤ ‖ρ‖ k^{−c−1}`, which is summable.
This is the "main term" half of the converse route: ψ(x) = x + E(x) splits the von Mangoldt
discrepancy into this piece plus an Abel sum against E (CV-2).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- The power-sum (ζ partial sum) discrepancy. -/
def zetaDiscrepancy (M : ℕ) (ρ : ℂ) : ℂ :=
  (∑ k ∈ Finset.Ioc 0 M, (k:ℂ) ^ (-ρ)) - (((M:ℂ)) ^ (1 - ρ) - 1) / (1 - ρ)

/-- Pointwise: `‖x^{−ρ} − k^{−ρ}‖ ≤ ‖ρ‖ k^{−c−1}` for `k ≤ x ≤ k+1`, `Re ρ ≥ c > 0`. -/
theorem cpow_neg_sub_norm_le {ρ : ℂ} {c : ℝ} (hc : 0 < c) (hcρ : c ≤ ρ.re)
    {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ (k:ℝ) + 1) :
    ‖(x:ℂ) ^ (-ρ) - ((k:ℝ):ℂ) ^ (-ρ)‖ ≤ ‖ρ‖ * (k:ℝ) ^ (-c - 1) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hcρ
    linarith
  have hcond : -1 < (-ρ - 1).re ∨ ((-ρ - 1) ≠ -1 ∧ (0:ℝ) ∉ Set.uIcc (k:ℝ) x) := by
    right
    refine ⟨fun h => hρ0 (by linear_combination -h), ?_⟩
    rw [Set.uIcc_of_le hx1]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hint := integral_cpow hcond
  rw [show -ρ - 1 + 1 = -ρ by ring] at hint
  have hnρ : -ρ ≠ 0 := neg_ne_zero.mpr hρ0
  have hdiff : (x:ℂ) ^ (-ρ) - ((k:ℝ):ℂ) ^ (-ρ)
      = (-ρ) * ∫ t in (k:ℝ)..x, (t:ℂ) ^ (-ρ - 1) := by
    rw [hint]
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [mul_comm, div_mul_cancel₀ _ hnρ])
      | (rw [mul_div_cancel₀ _ hnρ])
  rw [hdiff, norm_mul, norm_neg]
  have hpt : ∀ t ∈ Set.uIoc (k:ℝ) x, ‖(t:ℂ) ^ (-ρ - 1)‖ ≤ (k:ℝ) ^ (-c - 1) := by
    intro t ht
    rw [Set.uIoc_of_le hx1] at ht
    have htpos : (0:ℝ) < t := by linarith [ht.1]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-ρ - 1).re = -ρ.re - 1 := by simp
    rw [hre]
    calc t ^ (-ρ.re - 1) ≤ t ^ (-c - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by linarith)
      _ ≤ (k:ℝ) ^ (-c - 1) := Real.rpow_le_rpow_of_nonpos hkpos ht.1.le (by linarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hxk : |x - (k:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hk0 : 0 ≤ (k:ℝ) ^ (-c - 1) := Real.rpow_nonneg hkpos.le _
  calc ‖ρ‖ * ‖∫ t in (k:ℝ)..x, (t:ℂ) ^ (-ρ - 1)‖
      ≤ ‖ρ‖ * ((k:ℝ) ^ (-c - 1) * |x - (k:ℝ)|) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ ≤ ‖ρ‖ * ((k:ℝ) ^ (-c - 1) * 1) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hxk hk0
    _ = ‖ρ‖ * (k:ℝ) ^ (-c - 1) := by ring

/-- Per term: `‖k^{−ρ} − mainIncr(1−ρ) k‖ ≤ ‖ρ‖ k^{−c−1}`. -/
theorem powerTerm_sub_mainIncr_norm_le {ρ : ℂ} {c : ℝ} (hc : 0 < c) (hcρ : c ≤ ρ.re)
    (hρ : ρ ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖(k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k‖ ≤ ‖ρ‖ * (k:ℝ) ^ (-c - 1) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hnot0 : (0:ℝ) ∉ Set.uIcc (k:ℝ) ((k:ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hI : IntervalIntegrable (fun x : ℝ => (x:ℂ) ^ (-ρ)) MeasureTheory.volume
      (k:ℝ) ((k:ℝ) + 1) := intervalIntegral.intervalIntegrable_cpow (Or.inr hnot0)
  have hconst : ∫ _x in (k:ℝ)..((k:ℝ) + 1), ((k:ℝ):ℂ) ^ (-ρ) = ((k:ℝ):ℂ) ^ (-ρ) := by
    rw [intervalIntegral.integral_const, show (k:ℝ) + 1 - (k:ℝ) = 1 by ring, one_smul]
  have hC : IntervalIntegrable (fun _ : ℝ => ((k:ℝ):ℂ) ^ (-ρ)) MeasureTheory.volume
      (k:ℝ) ((k:ℝ) + 1) := by
    first
      | exact intervalIntegrable_const
      | simp
  rw [← Complex.ofReal_natCast k, mainIncr_eq_integral hρ hk, ← hconst,
    ← intervalIntegral.integral_sub hC hI]
  have hpt : ∀ x ∈ Set.uIoc (k:ℝ) ((k:ℝ) + 1),
      ‖((k:ℝ):ℂ) ^ (-ρ) - (x:ℂ) ^ (-ρ)‖ ≤ ‖ρ‖ * (k:ℝ) ^ (-c - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    rw [norm_sub_rev]
    exact cpow_neg_sub_norm_le hc hcρ hk hx.1.le hx.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show (k:ℝ) + 1 - (k:ℝ) = 1 by ring, abs_one, mul_one] at h
  exact h

/-- Decomposition: `zetaDiscrepancy M ρ = M^{−ρ} + Σ_{1≤k<M} (k^{−ρ} − mainIncr(1−ρ) k)`. -/
theorem zetaDiscrepancy_eq (ρ : ℂ) {M : ℕ} (hM : 1 ≤ M) :
    zetaDiscrepancy M ρ
      = (M:ℂ) ^ (-ρ) + ∑ k ∈ Finset.Ico 1 M, ((k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k) := by
  unfold zetaDiscrepancy
  have hIoc : Finset.Ioc 0 M = Finset.Ico 1 (M + 1) := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_succ_top hM, ← sum_Ico_mainIncr (1 - ρ) hM,
    Finset.sum_sub_distrib]
  ring

/-- **CV-1**: the power-sum discrepancy is bounded on `{c ≤ Re ρ, ‖ρ‖ ≤ R, ρ ≠ 1}`. -/
theorem zetaDiscrepancy_bounded {c R : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, ∀ ρ : ℂ, c ≤ ρ.re → ‖ρ‖ ≤ R → ρ ≠ 1 →
      ∀ M : ℕ, 1 ≤ M → ‖zetaDiscrepancy M ρ‖ ≤ B := by
  have hsum0 := summable_shifted_rpow (2 * c) (by linarith) 1
  have hsum : Summable (fun k : ℕ => ((k:ℝ) + 1) ^ (-(1 + 2 * c / 2))) :=
    hsum0.congr (fun k => one_mul _)
  set T : ℝ := ∑' k : ℕ, ((k:ℝ) + 1) ^ (-(1 + 2 * c / 2)) with hT
  refine ⟨1 + max R 0 * T, fun ρ hcρ hR hρ M hM => ?_⟩
  rw [zetaDiscrepancy_eq ρ hM]
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hfirst : ‖(M:ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_le_one_of_one_le_of_nonpos hM1
    simp only [Complex.neg_re]
    linarith
  have hterms : ∀ k ∈ Finset.Ico 1 M,
      ‖(k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k‖ ≤ max R 0 * (k:ℝ) ^ (-c - 1) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkpos : (0:ℝ) < (k:ℝ) := by
      have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
      linarith
    refine le_trans (powerTerm_sub_mainIncr_norm_le hc hcρ hρ hk1) ?_
    exact mul_le_mul_of_nonneg_right (le_trans hR (le_max_left _ _))
      (Real.rpow_nonneg hkpos.le _)
  have hreindex : ∑ k ∈ Finset.Ico 1 M, (k:ℝ) ^ (-c - 1)
      = ∑ j ∈ Finset.range (M - 1), ((j:ℝ) + 1) ^ (-(1 + 2 * c / 2)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    congr 1 <;> ring
  have hpartial : ∑ k ∈ Finset.Ico 1 M, (k:ℝ) ^ (-c - 1) ≤ T := by
    rw [hreindex, hT]
    exact hsum.sum_le_tsum _ (fun j _ => by
      have : (0:ℝ) < (j:ℝ) + 1 := by positivity
      exact Real.rpow_nonneg this.le _)
  have hsecond : ‖∑ k ∈ Finset.Ico 1 M, ((k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k)‖
      ≤ max R 0 * T := by
    calc ‖∑ k ∈ Finset.Ico 1 M, ((k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k)‖
        ≤ ∑ k ∈ Finset.Ico 1 M, ‖(k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico 1 M, max R 0 * (k:ℝ) ^ (-c - 1) := Finset.sum_le_sum hterms
      _ = max R 0 * ∑ k ∈ Finset.Ico 1 M, (k:ℝ) ^ (-c - 1) := by rw [Finset.mul_sum]
      _ ≤ max R 0 * T := mul_le_mul_of_nonneg_left hpartial (le_max_right _ _)
  calc ‖(M:ℂ) ^ (-ρ) + ∑ k ∈ Finset.Ico 1 M, ((k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k)‖
      ≤ ‖(M:ℂ) ^ (-ρ)‖ + ‖∑ k ∈ Finset.Ico 1 M, ((k:ℂ) ^ (-ρ) - mainIncr (1 - ρ) k)‖ :=
        norm_add_le _ _
    _ ≤ 1 + max R 0 * T := add_le_add hfirst hsecond

#print axioms cpow_neg_sub_norm_le
#print axioms powerTerm_sub_mainIncr_norm_le
#print axioms zetaDiscrepancy_bounded

end

end RHFormalization
