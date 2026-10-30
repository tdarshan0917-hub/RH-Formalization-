import RHFormalization.PolylogMainTermSum
import RHFormalization.PolylogShiftIdentity
import Mathlib

/-!
# PolylogShiftTheorem — PL-5a: polylog discrepancy at ρ ⟹ bounded discrepancy at ρ + δ

`vmDiscrepancy M ρ := Σ_{0<k≤M} Λ(k) k^{−ρ} − (M^{1−ρ} − 1)/(1−ρ)`.
If `‖vmDiscrepancy (m+1) ρ‖ ≤ C·(log(m+1))^A` for all `m`, then
`‖vmDiscrepancy M (ρ+δ)‖ ≤ C·K₀(δ,A) + 1` for every `M ≥ 1`, with a constant that does
not depend on `ρ`.  Assembly of PL-1/PL-2 (Abel), PL-4a (shift) and PL-4b-ii (main term).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Normalized von Mangoldt discrepancy. -/
def vmDiscrepancy (M : ℕ) (ρ : ℂ) : ℂ :=
  (∑ k ∈ Finset.Ioc 0 M,
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ k)
    - (((M:ℂ)) ^ (1 - ρ) - 1) / (1 - ρ)

/-- Centered sequence whose partial sums are the discrepancy. -/
def centeredVM (ρ : ℂ) (j : ℕ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ (j + 1)
    - (if j = 0 then 0 else mainIncr (1 - ρ) j)

theorem sum_Ico_mainIncr (z : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico 1 n, mainIncr z k = (((n:ℂ)) ^ z - 1) / z := by
  have h := sum_mainIncr z n
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)] at h
  have h0 : mainIncr z 0 = (1 - (0:ℂ) ^ z) / z := by
    unfold mainIncr
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow]
  rw [h0] at h
  simp only [zero_add] at h
  linear_combination h

theorem centeredVM_partialSum (ρ : ℂ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), centeredVM ρ j = vmDiscrepancy (m + 1) ρ := by
  unfold vmDiscrepancy
  have h1 : ∑ j ∈ Finset.range (m + 1), centeredVM ρ j
      = ∑ j ∈ Finset.range (m + 1),
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ (j + 1)
        - ∑ j ∈ Finset.range (m + 1), (if j = 0 then 0 else mainIncr (1 - ρ) j) := by
    simp only [centeredVM, Finset.sum_sub_distrib]
  have h2 : ∑ j ∈ Finset.range (m + 1), (if j = 0 then (0:ℂ) else mainIncr (1 - ρ) j)
      = ∑ j ∈ Finset.Ico 1 (m + 1), mainIncr (1 - ρ) j := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1),
      if_pos rfl]
    simp only [zero_add]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_Ico.mp hj).1
      omega
    rw [if_neg hj0]
  rw [h1, h2, sum_Ico_mainIncr (1 - ρ) (by omega : 1 ≤ m + 1),
    sum_Ioc_eq_sum_range_succ
      (fun k => LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ k) (m + 1)]

theorem vmDiscrepancy_shift_eq (ρ : ℂ) (δ : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    vmDiscrepancy M (ρ + (δ:ℂ))
      = ∑ j ∈ Finset.range M, centeredVM ρ j * ((((j:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)
        + ∑ k ∈ Finset.Ico 1 M,
            (mainIncr (1 - ρ) k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)
              - mainIncr (1 - (ρ + (δ:ℂ))) k) := by
  unfold vmDiscrepancy
  rw [partialSum_shift_eq ρ δ M, ← sum_Ico_mainIncr (1 - (ρ + (δ:ℂ))) hM]
  have h1 : ∑ j ∈ Finset.range M, centeredVM ρ j * ((((j:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range M,
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ (j + 1)
            * ((((j:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)
        - ∑ j ∈ Finset.range M,
            (if j = 0 then (0:ℂ) else mainIncr (1 - ρ) j) * ((((j:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold centeredVM
    ring
  have h2 : ∑ j ∈ Finset.range M,
        (if j = 0 then (0:ℂ) else mainIncr (1 - ρ) j) * ((((j:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)
      = ∑ j ∈ Finset.Ico 1 M, mainIncr (1 - ρ) j * ((((j:ℝ) + 1) ^ (-δ) : ℝ) : ℂ) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < M), if_pos rfl]
    simp only [zero_mul, zero_add]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_Ico.mp hj).1
      omega
    rw [if_neg hj0]
  rw [h1, h2, Finset.sum_sub_distrib]
  ring

/-- PL-4b-i with an explicit constant (needed for uniformity in ρ). -/
theorem centered_abel_bound_explicit (b : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ) (A : ℕ) {C K0 : ℝ}
    (hC : 0 ≤ C)
    (hK0 : ∀ n : ℕ,
      (Real.log ((n:ℝ) + 1)) ^ A * ((n:ℝ) + 1) ^ (-δ)
        + ∑ k ∈ Finset.range n,
            (Real.log ((k:ℝ) + 1)) ^ A * (((k:ℝ) + 1) ^ (-δ) - ((k:ℝ) + 2) ^ (-δ))
      ≤ K0)
    (hb : ∀ m : ℕ, ‖∑ k ∈ Finset.range (m+1), b k‖ ≤ C * (Real.log ((m:ℝ) + 1)) ^ A)
    (n : ℕ) :
    ‖∑ k ∈ Finset.range (n+1), b k * ((((k:ℝ) + 1) ^ (-δ) : ℝ) : ℂ)‖ ≤ C * K0 := by
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

/-- **PL-5a**: polylog discrepancy at ρ ⟹ bounded discrepancy at ρ + δ, uniformly in ρ. -/
theorem shifted_vmDiscrepancy_uniform {δ : ℝ} (hδ : 0 < δ) (A : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ≠ 1 → ρ + (δ:ℂ) ≠ 1 →
      (∀ m : ℕ, ‖vmDiscrepancy (m + 1) ρ‖ ≤ C * (Real.log ((m:ℝ) + 1)) ^ A) →
      ∀ M : ℕ, 1 ≤ M → ‖vmDiscrepancy M (ρ + (δ:ℂ))‖ ≤ K := by
  obtain ⟨K0, hK0⟩ := polylog_abel_weights_bounded δ hδ A
  refine ⟨C * K0 + 1, fun ρ hre hρ hρδ hD M hM => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have hb : ∀ m : ℕ, ‖∑ k ∈ Finset.range (m + 1), centeredVM ρ k‖
      ≤ C * (Real.log ((m:ℝ) + 1)) ^ A := by
    intro m
    rw [centeredVM_partialSum]
    exact hD m
  have habel := centered_abel_bound_explicit (centeredVM ρ) hδ A hC hK0 hb N
  have hE := mainIncr_shift_sum_le (le_refl (0:ℝ)) hre hδ.le hρ hρδ (N + 1)
  rw [vmDiscrepancy_shift_eq ρ δ hM]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ C * K0 + 1 := add_le_add habel hE

#print axioms centeredVM_partialSum
#print axioms vmDiscrepancy_shift_eq
#print axioms shifted_vmDiscrepancy_uniform

end

end RHFormalization
