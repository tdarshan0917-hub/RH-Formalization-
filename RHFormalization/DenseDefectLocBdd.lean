/-
DENSE SCHEDULE — Brick D4b: the dense defect gate closes.
Defines the dense free paired transform and dense Galerkin transform defect
(instantiating the parametric decodedOneLetterTransform / windowedCanonicalPackage
at denseL/denseN — cutoff, codes, weights unchanged), proves the norm bound
‖defect‖ ≤ mass · perSpikeBound, and closes loc_bdd via D4a
(denseStageBound_uniform). First of the three certified endpoint inputs
rebuilt on the dense schedule.
-/

import RHFormalization.DenseGalerkinSchedule
import RHFormalization.DenseStageBoundUniform
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.ResolventDenomCompactLowerBound

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

/-- The dense free paired transform (dense analogue of
`adaptiveFreePairedTransform`; same cutoff, codes, weights). -/
def denseFreePairedTransform (n : ℕ) (s : ℂ) : ℂ :=
  decodedOneLetterTransform (N := denseN n)
    (fun m => galerkinLam (denseL n) (m : ℕ))
    (activePrimePowerPairsCenterBelow (admR n))
    (denseL n) s

/-- **THE DENSE GATE OBJECT**: dense free paired transform minus the
windowed canonical package at the dense window. -/
def denseGalerkinTransformDefect (n : ℕ) (s : ℂ) : ℂ :=
  denseFreePairedTransform n s
    - windowedCanonicalPackage
        (activePrimePowerPairsCenterBelow (admR n)) (denseL n)
        shiftedLaplaceHeatKernelC s

/-- The dense defect is the weighted sum of per-spike defects
(same `unfold + ring` algebra as the adaptive version; L-generic). -/
theorem denseDefect_eq_weighted_sum (n : ℕ) (s : ℂ) :
    denseGalerkinTransformDefect n s
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            (((1 / (2 * denseL n) : ℝ) : ℂ)
                * galerkinSpikeTransform (N := denseN n)
                    (fun m => galerkinLam (denseL n) (m : ℕ))
                    (denseL n) q.center s
              - (((denseL n - q.center) / (2 * denseL n) : ℝ) : ℂ)
                  * shiftedLaplaceHeatKernelC q.center s) := by
  unfold denseGalerkinTransformDefect denseFreePairedTransform
    decodedOneLetterTransform windowedCanonicalPackage
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- **Dense L2 — the stage-level defect bound** (mirror of
`adaptiveDefect_norm_le_stageBound`, dense floors supplying `a ≤ L`). -/
theorem denseDefect_norm_le_stageBound (n : ℕ) (s : ℂ)
    (hs : s ∈ Ω) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hfl : ∀ ξ : ℝ, c₀ * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖denseGalerkinTransformDefect n s‖
      ≤ adaptiveStageMass n
          * perSpikeBound (admR n) (denseL n) (denseN n) c₀ := by
  rw [denseDefect_eq_weighted_sum n s]
  have hL := denseL_pos n
  have hN := denseN_pos n
  have hRL : admR n ≤ denseL n := (admR_lt_denseL n).le
  have hspike : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC *
          (((1 / (2 * denseL n) : ℝ) : ℂ)
              * galerkinSpikeTransform (N := denseN n)
                  (fun m => galerkinLam (denseL n) (m : ℕ))
                  (denseL n) q.center s
            - (((denseL n - q.center) / (2 * denseL n) : ℝ) : ℂ)
                * shiftedLaplaceHeatKernelC q.center s)‖
        ≤ ‖q.weightC‖
            * perSpikeBound (admR n) (denseL n) (denseN n) c₀ := by
    intro q hq
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨_, hcR⟩ := (activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq
    have hc0 : (0:ℝ) ≤ q.center := center_nonneg q
    have hcL : q.center ≤ denseL n := le_trans hcR hRL
    have hmain := perSpikeTransformDefect_norm_le hN (denseL n) q.center
      hL hc0 hcL s hs c₀ hc₀ hfl
    exact hmain.trans (perSpikeBound_mono_center q.center (admR n)
      (denseL n) (denseN n) c₀ hc₀ hL hcR)
  calc ‖∑ q ∈ activePrimePowerPairsCenterBelow (admR n), _‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC‖ * perSpikeBound (admR n) (denseL n) (denseN n) c₀ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hspike)
    _ = adaptiveStageMass n
          * perSpikeBound (admR n) (denseL n) (denseN n) c₀ := by
        unfold adaptiveStageMass
        rw [← Finset.sum_mul]

/-- **DENSE loc_bdd — the dense defect gate closes** (via D4a). -/
theorem denseGalerkinTransformDefect_loc_bdd (K : Set ℂ)
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖denseGalerkinTransformDefect n s‖ ≤ C := by
  obtain ⟨c₀, hc₀, hfl⟩ := resolventDenom_lower_bound K hK hKΩ
  refine ⟨115 * (Real.log 4 + 4) / c₀ + 6 * (Real.log 4 + 4) / c₀ ^ 2, ?_⟩
  intro n s hs
  exact (denseDefect_norm_le_stageBound n s (hKΩ hs) c₀ hc₀
    (fun ξ => hfl s hs ξ)).trans (denseStageBound_uniform n c₀ hc₀)

#print axioms denseFreePairedTransform
#print axioms denseGalerkinTransformDefect
#print axioms denseDefect_eq_weighted_sum
#print axioms denseDefect_norm_le_stageBound
#print axioms denseGalerkinTransformDefect_loc_bdd

end

end RHFormalization
