-- SENTINEL: L2-adaptive-defect-stage-bound-v2
import RHFormalization.PerSpikeTransformDefectBound
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.AdaptiveStageMassBridge
import RHFormalization.AdaptiveWeightedDefectSum
import RHFormalization.AdaptiveScheduleGrowthBounds
import Mathlib

/-!
# L2 — The stage-level defect bound
`adaptiveDefect_norm_le_stageBound`: on any s ∈ Ω with floor c₀,
  ‖adaptiveGalerkinTransformDefect c n s‖
    ≤ adaptiveStageMass n · perSpikeBound(admR n, L n, N n, c₀),
where perSpikeBound is the L1e three-term expression evaluated at the
worst center a = admR n. The defect unfolds to Σ_q weightC·(per-spike
defect), the L1e bound is monotone in a on [0, admR n], and the triangle
inequality over the finite spike set closes it.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The per-spike bound as a named rate (a = worst center R). -/
def perSpikeBound (R L : ℝ) (N : ℕ) (c : ℝ) : ℝ :=
  (1 / (2 * L)) * ((R / c) * (Real.pi / 2) + 1 / c^2)
    + L / (2 * c * Real.pi^2 * (N : ℝ))
    + (1 / (2 * L * c * Real.pi)) * (1 + Real.log N)

/-- The defect is the weighted sum of per-spike defects. -/
theorem adaptiveDefect_eq_weighted_sum (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveGalerkinTransformDefect c n s
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)
                * galerkinSpikeTransform (N := adaptiveN c n)
                    (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
                    (adaptiveL c n) q.center s
              - (((adaptiveL c n - q.center) / (2 * adaptiveL c n) : ℝ) : ℂ)
                  * shiftedLaplaceHeatKernelC q.center s) := by
  unfold adaptiveGalerkinTransformDefect adaptiveFreePairedTransform
    decodedOneLetterTransform windowedCanonicalPackage
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Monotonicity of the L1e bound in the center a (only the (a/c) term moves). -/
theorem perSpikeBound_mono_center (a R L : ℝ) (N : ℕ) (c : ℝ) (hc : 0 < c)
    (hL : 0 < L) (haR : a ≤ R) :
    (1 / (2 * L)) * ((a / c) * (Real.pi / 2) + 1 / c^2)
        + L / (2 * c * Real.pi^2 * (N : ℝ))
        + (1 / (2 * L * c * Real.pi)) * (1 + Real.log N)
      ≤ perSpikeBound R L N c := by
  unfold perSpikeBound
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hstep : (a / c) * (Real.pi / 2) ≤ (R / c) * (Real.pi / 2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact div_le_div_of_nonneg_right haR hc.le
  have h2L : (0:ℝ) < 1 / (2 * L) := by positivity
  nlinarith [h2L, hstep]

/-- **L2 — the stage-level defect bound.** -/
theorem adaptiveDefect_norm_le_stageBound (c : ℝ) (n : ℕ) (s : ℂ)
    (hs : s ∈ Ω) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hfl : ∀ ξ : ℝ, c₀ * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖adaptiveGalerkinTransformDefect c n s‖
      ≤ adaptiveStageMass n
          * perSpikeBound (admR n) (adaptiveL c n) (adaptiveN c n) c₀ := by
  rw [adaptiveDefect_eq_weighted_sum c n s]
  have hL := adaptiveL_pos c n
  have hN := adaptiveN_pos c n
  have hRL := admR_le_adaptiveL c n
  -- per-spike bound at each q
  have hspike : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC *
          (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)
              * galerkinSpikeTransform (N := adaptiveN c n)
                  (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
                  (adaptiveL c n) q.center s
            - (((adaptiveL c n - q.center) / (2 * adaptiveL c n) : ℝ) : ℂ)
                * shiftedLaplaceHeatKernelC q.center s)‖
        ≤ ‖q.weightC‖
            * perSpikeBound (admR n) (adaptiveL c n) (adaptiveN c n) c₀ := by
    intro q hq
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨_, hcR⟩ := (activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq
    have hc0 : (0:ℝ) ≤ q.center := center_nonneg q
    have hcL : q.center ≤ adaptiveL c n := le_trans hcR hRL
    have hmain := perSpikeTransformDefect_norm_le hN (adaptiveL c n) q.center
      hL hc0 hcL s hs c₀ hc₀ hfl
    exact hmain.trans (perSpikeBound_mono_center q.center (admR n)
      (adaptiveL c n) (adaptiveN c n) c₀ hc₀ hL hcR)
  -- triangle inequality + factor out the constant
  calc ‖∑ q ∈ activePrimePowerPairsCenterBelow (admR n), _‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC‖ * perSpikeBound (admR n) (adaptiveL c n) (adaptiveN c n) c₀ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hspike)
    _ = adaptiveStageMass n
          * perSpikeBound (admR n) (adaptiveL c n) (adaptiveN c n) c₀ := by
        unfold adaptiveStageMass
        rw [← Finset.sum_mul]

#print axioms adaptiveDefect_eq_weighted_sum
#print axioms perSpikeBound_mono_center
#print axioms adaptiveDefect_norm_le_stageBound

end

end RHFormalization
