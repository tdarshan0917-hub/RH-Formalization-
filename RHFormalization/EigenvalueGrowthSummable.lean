import RHFormalization.BallCutDistance
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace RHFormalization

noncomputable section

theorem summable_inv_nsq_add_one :
    Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 1)⁻¹) := by
  -- shift by 1 so the dominating term (n+1)^2 is never zero
  rw [← summable_nat_add_iff 1]
  have hp : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
      (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    rw [← summable_nat_add_iff 1] at h2
    refine h2.congr (fun n => ?_)
    push_cast
    ring_nf
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hp
  have hb1 : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have hle : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 + 1 := by linarith
  have hcast : (((n : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact inv_anti₀ hb1 hle


theorem summable_resolvent_of_weyl
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 ≤ lam n)
    (c C : ℝ) (hc : 0 < c)
    (hweyl : ∀ n : ℕ, c * (n : ℝ) ^ 2 - C ≤ lam n) :
    Summable (fun n => (1 + lam n)⁻¹) := by
  set D : ℝ := max 0 C with hDdef
  have hD0 : 0 ≤ D := le_max_left _ _
  have hDC : C ≤ D := le_max_right _ _
  set K : ℝ := (1 + D + c) / c with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hbase : Summable (fun n : ℕ => K * ((n : ℝ) ^ 2 + 1)⁻¹) :=
    summable_inv_nsq_add_one.mul_left K
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · have := hlam n; positivity
  have hden_pos : (0:ℝ) < 1 + lam n := by have := hlam n; linarith
  have hnsq_pos : (0:ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
  have hlamn : 0 ≤ lam n := hlam n
  have hw : c * (n : ℝ) ^ 2 - C ≤ lam n := hweyl n
  -- from Weyl: c·n² ≤ lam n + D  (since C ≤ D)
  have hcn2 : c * (n:ℝ)^2 ≤ lam n + D := by linarith [hw, hDC]
  -- scalar core: (n²+1) ≤ K (1+λ), i.e. (n²+1)c ≤ (1+D+c)(1+λ)
  have key : ((n : ℝ) ^ 2 + 1) ≤ K * (1 + lam n) := by
    rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ hc]
    -- goal: (n²+1)*c ≤ (1+D+c)*(1+λ)
    -- (n²+1)c = c·n² + c ≤ (λ+D) + c ≤ (1+D+c)(1+λ)
    nlinarith [hcn2, hlamn, hD0, hc,
               mul_nonneg (mul_nonneg hlamn hlamn) hc.le,
               mul_nonneg hlamn hD0, mul_nonneg hlamn hc.le]
  have hinv : (K * (1 + lam n))⁻¹ ≤ ((n : ℝ) ^ 2 + 1)⁻¹ := inv_anti₀ hnsq_pos key
  have h := mul_le_mul_of_nonneg_left hinv (le_of_lt hKpos)
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hKpos), one_mul] at h
  exact h

#print axioms summable_inv_nsq_add_one
#print axioms summable_resolvent_of_weyl

/-- **Operator-side holomorphy from the Weyl bound alone.** Composing Lemma
A.GROWTH with `Fstage_holo_from_summable`: the eigenvalue-sum transform
`∑ₙ 1/(s+λₙ)` is holomorphic on `Ω` given only the Weyl growth bound
`λₙ ≥ c·n² - C` (c>0) and `λₙ ≥ 0`. No summability hypothesis, no per-ball
input, no zero-location content. -/
theorem Fstage_holo_from_weyl
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 ≤ lam n)
    (c C : ℝ) (hc : 0 < c)
    (hweyl : ∀ n : ℕ, c * (n : ℝ) ^ 2 - C ≤ lam n) :
    HolomorphicOnC (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) Ω :=
  Fstage_holo_from_summable lam hlam (summable_resolvent_of_weyl lam hlam c C hc hweyl)

#print axioms Fstage_holo_from_weyl


end

end RHFormalization
