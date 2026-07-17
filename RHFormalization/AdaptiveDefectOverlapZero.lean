-- SENTINEL: E3c-v2
import RHFormalization.AdaptiveDefectHalfplaneBound
import RHFormalization.AdaptiveOverlapRateBound
import Mathlib

/-!
# Half-plane vanishing of the adaptive defect (defect-gate overlap0)

On U = {Re s > 1} ⊆ Ω: ‖defect_n(s)‖ ≤ 40/√(n+2) → 0. GPT's exact
Montel-input shape.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Filter

/-- On `Re s > 1`, E2's δ-dependent bound is at most the s-free rate. -/
theorem rateBound_le_overlapRate (c : ℝ) (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    (1 / (2 * adaptiveL c n)) * (1/(s.re + 1/4))
      + (Real.pi * admR n / (2 * adaptiveL c n))
          * (s.re + 1/4) ^ (-(1/2) : ℝ)
      + 1 / ((adaptiveN c n : ℝ) * (Real.pi / adaptiveL c n))
      + ((1 + Real.log (adaptiveN c n))
          / (2 * Real.pi * adaptiveL c n)) * (1/(s.re + 1/4))
    ≤ overlapRateBound c n := by
  have hδ1 : (1:ℝ) ≤ s.re + 1/4 := by linarith
  have hδ0 : (0:ℝ) < s.re + 1/4 := by linarith
  have hL : (0:ℝ) < adaptiveL c n := adaptiveL_pos c n
  have hR0 : (0:ℝ) ≤ admR n := by
    have hadmR : admR n = Real.log ((n : ℝ) + 2) / 2 := by
      unfold admR; norm_num
    rw [hadmR]
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have : (0:ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    linarith
  have hlogN0 : (0:ℝ) ≤ 1 + Real.log (adaptiveN c n) := by
    have : (0:ℝ) ≤ Real.log ((adaptiveN c n : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast adaptiveN_pos c n
    linarith
  have hinv : 1/(s.re + 1/4) ≤ 1 := by
    rw [div_le_one hδ0]
    linarith
  have hrpow : (s.re + 1/4) ^ (-(1/2) : ℝ) ≤ 1 := by
    first
      | exact Real.rpow_le_one_of_one_le_of_nonpos hδ1 (by norm_num)
      | (rw [Real.rpow_neg hδ0.le]
         apply inv_le_one_of_one_le
         exact Real.one_le_rpow hδ1 (by norm_num))
      | (rw [Real.rpow_neg hδ0.le, ← Real.sqrt_eq_rpow]
         rw [inv_le_one_iff₀]
         right
         nlinarith [Real.sqrt_nonneg (s.re + 1/4),
           Real.sq_sqrt hδ0.le, hδ1])
  unfold overlapRateBound
  have h1 : (1 / (2 * adaptiveL c n)) * (1/(s.re + 1/4))
      ≤ 1 / (2 * adaptiveL c n) := by
    calc (1 / (2 * adaptiveL c n)) * (1/(s.re + 1/4))
        ≤ (1 / (2 * adaptiveL c n)) * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 1 / (2 * adaptiveL c n) := mul_one _
  have h2 : (Real.pi * admR n / (2 * adaptiveL c n))
        * (s.re + 1/4) ^ (-(1/2) : ℝ)
      ≤ Real.pi * admR n / (2 * adaptiveL c n) := by
    calc (Real.pi * admR n / (2 * adaptiveL c n))
          * (s.re + 1/4) ^ (-(1/2) : ℝ)
        ≤ (Real.pi * admR n / (2 * adaptiveL c n)) * 1 :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = Real.pi * admR n / (2 * adaptiveL c n) := mul_one _
  have h4 : ((1 + Real.log (adaptiveN c n))
        / (2 * Real.pi * adaptiveL c n)) * (1/(s.re + 1/4))
      ≤ (1 + Real.log (adaptiveN c n))
          / (2 * Real.pi * adaptiveL c n) := by
    have hnn : (0:ℝ) ≤ (1 + Real.log (adaptiveN c n))
        / (2 * Real.pi * adaptiveL c n) := by
      apply div_nonneg hlogN0
      positivity
    calc ((1 + Real.log (adaptiveN c n))
            / (2 * Real.pi * adaptiveL c n)) * (1/(s.re + 1/4))
        ≤ ((1 + Real.log (adaptiveN c n))
            / (2 * Real.pi * adaptiveL c n)) * 1 :=
          mul_le_mul_of_nonneg_left hinv hnn
      _ = (1 + Real.log (adaptiveN c n))
            / (2 * Real.pi * adaptiveL c n) := mul_one _
  linarith [h1, h2, h4]

/-- The scalar rate tends to zero. -/
theorem overlapRate_tendsto_zero :
    Tendsto (fun n : ℕ => (40:ℝ) / Real.sqrt ((n : ℝ) + 2))
      atTop (nhds 0) := by
  apply Tendsto.div_atTop (tendsto_const_nhds)
  apply Real.tendsto_sqrt_atTop.comp
  apply tendsto_atTop_add_const_right
  exact tendsto_natCast_atTop_atTop

/-- **OVERLAP0 — the Montel-input half-plane vanishing.** -/
theorem adaptiveGalerkinTransformDefect_overlap0 (c : ℝ) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Omega ∧
      ∀ s ∈ U, Tendsto
        (fun n => adaptiveGalerkinTransformDefect c n s)
        atTop (nhds 0) := by
  refine ⟨{s : ℂ | 1 < s.re}, ?_, ?_, ?_, ?_⟩
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact ⟨2, by norm_num⟩
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs
    intro hmem
    have hre : s.re ≤ 0 := by
      first
        | exact hmem.2.le
        | exact hmem.1
        | (obtain ⟨hre, _⟩ := hmem; linarith)
        | (unfold NonpositiveRealAxis at hmem
           simp only [Set.mem_setOf_eq] at hmem
           linarith [hmem.1])
    linarith
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have hs0 : 0 < s.re := by linarith
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) overlapRate_tendsto_zero
    calc ‖adaptiveGalerkinTransformDefect c n s‖
        ≤ adaptiveStageMass n *
            ((1 / (2 * adaptiveL c n)) * (1/(s.re + 1/4))
              + (Real.pi * admR n / (2 * adaptiveL c n))
                  * (s.re + 1/4) ^ (-(1/2) : ℝ)
              + 1 / ((adaptiveN c n : ℝ) * (Real.pi / adaptiveL c n))
              + ((1 + Real.log (adaptiveN c n))
                  / (2 * Real.pi * adaptiveL c n)) * (1/(s.re + 1/4))) :=
          adaptiveDefect_norm_le c n s hs0
      _ ≤ adaptiveStageMass n * overlapRateBound c n := by
          apply mul_le_mul_of_nonneg_left
            (rateBound_le_overlapRate c n s hs)
          unfold adaptiveStageMass
          exact Finset.sum_nonneg fun q _ => norm_nonneg _
      _ ≤ 40 / Real.sqrt ((n : ℝ) + 2) := mass_mul_overlapRate_le c n

#print axioms rateBound_le_overlapRate
#print axioms overlapRate_tendsto_zero
#print axioms adaptiveGalerkinTransformDefect_overlap0

end

end RHFormalization
