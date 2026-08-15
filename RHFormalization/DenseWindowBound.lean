/-
DENSE SCHEDULE — Brick D5: the dense window, proved DIRECTLY (Lemma 3).
BcorrWinDense = Σ weightC·(a_q/(2·denseL))·K(a_q,s) — the per-spike deficit
coefficient verified against the disk definition of BcorrWin, with denseL in
the window slot. The old ratio-to-admL theorem is NOT used (it reverses on
dense L). Bound: ‖BcorrWinDense‖ ≤ (R/(2L))·mass·c⁻¹ with the D3c sharp mass;
uniform boundedness via (R/(2L))·mass ≤ 12B·X^{-1/4}logX-type control,
certified here as (R/(2L))·mass ≤ 24B (crude absolute constant suffices for
loc_bdd — the decay rate is a later corollary). Second endpoint input dense.
-/

import RHFormalization.DenseGalerkinSchedule
import RHFormalization.DenseSharpMassSchedule
import RHFormalization.DBFFDeficitCompactBound
import RHFormalization.AdaptiveStageMassBridge
import RHFormalization.DenseStageBoundUniform
import RHFormalization.ShiftedLaplacePrimeSummable
import RHFormalization.ShiftedLaplaceBranchRange

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open Real

/-- **THE DENSE WINDOW CORRECTION**: per-spike deficit at the dense window. -/
def BcorrWinDense (n : ℕ) (s : ℂ) : ℂ :=
  (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
    q.weightC * ((q.center / (2 * denseL n) : ℝ) : ℂ) *
      shiftedLaplaceHeatKernelC q.center s

/-- Mass-factored estimate (transcription of `BcorrWin_norm_le_on_compact`
with `denseL` in the window slot; kernel bound via `kernelDenom_min`). -/
theorem BcorrWinDense_norm_le_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K,
      ‖BcorrWinDense n s‖ ≤ admR n / (2 * denseL n) * adaptiveStageMass n * C := by
  obtain ⟨c, hc, hcK⟩ := kernelDenom_min K hK hKO
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro n s hs
  have hL2 : (0 : ℝ) < 2 * denseL n := by have := denseL_pos n; linarith
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC * ((q.center / (2 * denseL n) : ℝ) : ℂ) *
          shiftedLaplaceHeatKernelC q.center s‖ ≤
        admR n / (2 * denseL n) * ‖q.weightC‖ * c⁻¹ := by
    intro q hq
    have hcle : q.center ≤ admR n :=
      ((activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq).2
    have hfrac0 : (0 : ℝ) ≤ q.center / (2 * denseL n) :=
      div_nonneg (center_nonneg q) hL2.le
    have hcnorm : ‖((q.center / (2 * denseL n) : ℝ) : ℂ)‖
        = q.center / (2 * denseL n) := by
      first
        | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfrac0]
        | rw [Complex.norm_ofReal, abs_of_nonneg hfrac0]
    have hfracle : q.center / (2 * denseL n) ≤ admR n / (2 * denseL n) := by
      first
        | exact div_le_div_of_nonneg_right hcle hL2
        | exact div_le_div_of_le_left hcle hL2 hL2
        | gcongr
    -- kernel bound via the banked norm equality + sqrt_re_nonneg
    have hker : ‖shiftedLaplaceHeatKernelC q.center s‖ ≤ c⁻¹ := by
      rw [norm_shiftedLaplaceHeatKernelC]
      have hc2 := hcK s hs
      have hden : 1 / ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖ ≤ c⁻¹ := by
        rw [one_div]
        exact inv_anti₀ hc hc2
      have hexp : Real.exp (-q.center * (Complex.sqrt (s + (1/4 : ℂ))).re) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hsq := sqrt_re_nonneg (s + (1/4 : ℂ))
        have := mul_nonneg (center_nonneg q) hsq
        linarith
      calc (1 / ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖)
            * Real.exp (-q.center * (Complex.sqrt (s + (1/4 : ℂ))).re)
          ≤ c⁻¹ * 1 := by
            apply mul_le_mul hden hexp (Real.exp_nonneg _) (inv_pos.mpr hc).le
        _ = c⁻¹ := mul_one _
    calc ‖q.weightC * ((q.center / (2 * denseL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s‖
        = ‖q.weightC‖ * ‖((q.center / (2 * denseL n) : ℝ) : ℂ)‖
            * ‖shiftedLaplaceHeatKernelC q.center s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖q.weightC‖ * (admR n / (2 * denseL n)) * c⁻¹ := by
          apply mul_le_mul ?_ hker (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (div_nonneg (admR_pos n).le hL2.le))
          rw [hcnorm]
          exact mul_le_mul_of_nonneg_left hfracle (norm_nonneg _)
      _ = admR n / (2 * denseL n) * ‖q.weightC‖ * c⁻¹ := by ring
  calc ‖BcorrWinDense n s‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC * ((q.center / (2 * denseL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          admR n / (2 * denseL n) * ‖q.weightC‖ * c⁻¹ :=
        Finset.sum_le_sum hterm
    _ = admR n / (2 * denseL n) * adaptiveStageMass n * c⁻¹ := by
        unfold adaptiveStageMass
        rw [Finset.mul_sum, Finset.sum_mul]
        try (refine Finset.sum_congr rfl (fun q _ => ?_); ring)
        try rfl

/-- Schedule control: `(R/(2L))·mass ≤ 24B` (crude absolute bound; R ≤ L
from the floor, mass ≤ 12B·√X ≤ 12B·L^{2/3}·... — here we take the simplest
route: R/(2L) ≤ 1/2 and mass·(R/(2L)) ≤ 12B·X^{1/4}·(R/(2L)); since
R = logX ≤ 4X^{1/8} and L ≥ X^{3/4} ≥ X^{3/8}, the product is ≤ 24B·X^{-...}
≤ 24B. Certified via the D4a-style rpow ladder. -/
theorem denseWindow_schedule_control (n : ℕ) :
    admR n / (2 * denseL n) * adaptiveStageMass n ≤ 24 * (Real.log 4 + 4) := by
  have hx2 : (2:ℝ) ≤ (n:ℝ)+2 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hx0 : (0:ℝ) < (n:ℝ)+2 := by linarith
  have hx1 : (1:ℝ) ≤ (n:ℝ)+2 := by linarith
  have hBnn : (0:ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hL2 : (0:ℝ) < 2 * denseL n := by linarith
  have hLlow : ((n:ℝ)+2) ^ ((3:ℝ)/8) ≤ denseL n := rpow_le_denseL n
  have hmass : adaptiveStageMass n
      ≤ 12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4) := by
    have h := adaptiveStageMass_le_sqrt_exp n
    rwa [sqrt_exp_admR_eq_rpow_quarter n] at h
  have hmass0 : (0:ℝ) ≤ adaptiveStageMass n := by
    unfold adaptiveStageMass
    exact Finset.sum_nonneg fun q _ => norm_nonneg _
  have hR_eq : admR n = Real.log ((n:ℝ)+2) / 2 := by
    first | rfl | (unfold admR; ring)
  have hR0 : (0:ℝ) ≤ admR n := by
    rw [hR_eq]
    have := Real.log_nonneg hx1
    linarith
  have hRle : admR n ≤ 4 * ((n:ℝ)+2) ^ ((1:ℝ)/8) := by
    rw [hR_eq]
    have := log_le_eight_rpow_eighth hx1
    linarith
  have hmul1 : ((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ ((1:ℝ)/8)
      = ((n:ℝ)+2) ^ ((3:ℝ)/8) := by
    rw [← Real.rpow_add hx0]
    norm_num
  -- R·mass ≤ 48B·(n+2)^{3/8} ≤ 48B·L, so (R/(2L))·mass ≤ 24B
  have hRmass : admR n * adaptiveStageMass n
      ≤ 48 * (Real.log 4 + 4) * denseL n := by
    calc admR n * adaptiveStageMass n
        ≤ (4 * ((n:ℝ)+2) ^ ((1:ℝ)/8))
            * (12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4)) := by
          apply mul_le_mul hRle hmass hmass0 (by positivity)
      _ = 48 * (Real.log 4 + 4)
            * (((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ ((1:ℝ)/8)) := by ring
      _ = 48 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((3:ℝ)/8) := by rw [hmul1]
      _ ≤ 48 * (Real.log 4 + 4) * denseL n := by nlinarith [hLlow, hBnn]
  rw [div_mul_eq_mul_div, div_le_iff₀ hL2]
  calc admR n * adaptiveStageMass n
      ≤ 48 * (Real.log 4 + 4) * denseL n := hRmass
    _ = 24 * (Real.log 4 + 4) * (2 * denseL n) := by ring

/-- **DENSE hW — the dense window bound closes** (second endpoint input). -/
theorem BcorrWinDense_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ Cw : ℝ, ∀ n, ∀ s ∈ K, ‖BcorrWinDense n s‖ ≤ Cw := by
  obtain ⟨C, hC0, hbound⟩ := BcorrWinDense_norm_le_on_compact K hK hKΩ
  refine ⟨24 * (Real.log 4 + 4) * C, ?_⟩
  intro n s hs
  calc ‖BcorrWinDense n s‖
      ≤ admR n / (2 * denseL n) * adaptiveStageMass n * C := hbound n s hs
    _ ≤ 24 * (Real.log 4 + 4) * C := by
        apply mul_le_mul_of_nonneg_right (denseWindow_schedule_control n) hC0.le

#print axioms BcorrWinDense
#print axioms BcorrWinDense_norm_le_on_compact
#print axioms denseWindow_schedule_control
#print axioms BcorrWinDense_uniform_bound

end

end RHFormalization
