-- SENTINEL: decoded-prime-split-v1
import RHFormalization.DecodedAdaptiveCombinedFreeR
import RHFormalization.AdaptivePrimeSplitIdentity
import RHFormalization.DecodedEigenvalueFloor
import Mathlib

/-!
# DecodedAdaptivePrimeSplit — FOW + O2res at the decoded operator
The split engine (`resolvent_sub_eq_first_plus_second`) is generic in
(μ, hV); this brick instantiates it at the DECODED potential
`decodedGalerkinVC` on the decoded adaptive stage. Identity only.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- Decoded first-order window: `−density·Tr(R_D V_dec R_D)` at `s+SupVConst`. -/
def decodedAdaptiveFirstOrderWindow (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  -(adaptiveDensityC c n *
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (adaptiveN c n)))
      (freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
          (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (decodedGalerkinVC (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
        * freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (s + (SupVConst : ℂ))))

/-- Decoded second-resolvent residual: `+density·Tr(R_D V_dec R_H^dec V_dec R_D)`. -/
def decodedAdaptiveSecondResolventResidual (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  adaptiveDensityC c n *
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (adaptiveN c n)))
      (freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
          (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (decodedGalerkinVC (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
        * perturbedResolventOp (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (decodedGalerkinVC_isHermitian (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
            (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (decodedGalerkinVC (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
        * freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (s + (SupVConst : ℂ)))

/-- Decoded short residual (assembled). -/
def decodedAdaptiveShortResidual (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  decodedAdaptiveFirstOrderWindow c n s
    + decodedAdaptiveSecondResolventResidual c n s

/-- **THE DECODED SPLIT**: `decodedPrime = decodedFOW + decodedO2res` on Ω. -/
theorem decodedFadmPrimeStage_eq_first_plus_second
    (c : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    decodedFadmPrimeStage c n s
      = decodedAdaptiveFirstOrderWindow c n s
        + decodedAdaptiveSecondResolventResidual c n s := by
  set μ := galerkinFreeMu (adaptiveN c n) (adaptiveL c n) with hμdef
  set hV := decodedGalerkinVC_isHermitian (N := adaptiveN c n) 1
    (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (adaptiveL c n)
    with hVdef
  set w : ℂ := s + (SupVConst : ℂ) with hwdef
  have hμnn : ∀ k, 0 ≤ μ k := by
    intro k
    rw [hμdef]
    first
      | exact galerkinFreeMu_nonneg _ _ k
      | (unfold galerkinFreeMu; positivity)
      | exact sq_nonneg _
  have hneF : ∀ i, w + ((μ i : ℝ) : ℂ) ≠ 0 := by
    intro i
    have hcast : w + ((μ i : ℝ) : ℂ)
        = s + ((SupVConst + μ i : ℝ) : ℂ) := by
      rw [hwdef]; push_cast; ring
    rw [hcast]
    exact add_real_ne_zero_of_mem_Omega hs
      (add_nonneg SupVConst_nonneg_adm (hμnn i))
  have hneP : ∀ i, w + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0 := by
    intro i
    have hlamnn : 0 ≤ perturbedEigenvalues μ hV i := by
      first
        | exact decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n)
            (activePrimePowerCodesCenterBelow (admR n)) μ hμnn i
        | exact decodedAdmissibleEigenvalue_nonneg (adaptiveL c n)
            (adaptiveL_pos c n)
            (activePrimePowerCodesCenterBelow (admR n)) μ hμnn i
        | (rw [hVdef]
           exact decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n)
             (activePrimePowerCodesCenterBelow (admR n)) μ hμnn i)
    have hcast : w + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)
        = s + ((SupVConst + perturbedEigenvalues μ hV i : ℝ) : ℂ) := by
      rw [hwdef]; push_cast; ring
    rw [hcast]
    exact add_real_ne_zero_of_mem_Omega hs
      (add_nonneg SupVConst_nonneg_adm hlamnn)
  have hstep1 : decodedFadmPrimeStage c n s
      = adaptiveDensityC c n *
          (FstageFinite (perturbedEigenvalues μ hV) w - FstageFinite μ w) := by
    unfold decodedFadmPrimeStage
    rw [decodedAdaptiveGalerkinStageSeq_F_stage c n s]
    have hpert : decodedGalerkinPerturbedFStage
          (N := adaptiveN c n) μ 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (adaptiveL c n) (s + (SupVConst : ℂ))
        = FstageFinite (perturbedEigenvalues μ hV) w := by
      have hunf : decodedGalerkinPerturbedFStage
            (N := adaptiveN c n) μ 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (adaptiveL c n) (s + (SupVConst : ℂ))
          = perturbedFStage μ hV (s + (SupVConst : ℂ)) := by
        rw [hVdef]
        rfl
      rw [hunf, perturbedFStage_shift_eq μ hV SupVConst s]
      first
        | rw [FstageFinite_shift (perturbedEigenvalues μ hV) SupVConst s,
            ← hwdef]
        | (rw [← FstageFinite_shift (perturbedEigenvalues μ hV) SupVConst s,
            ← hwdef])
        | (unfold FstageFinite
           refine Finset.sum_congr rfl fun i _ => ?_
           rw [hwdef]
           congr 1
           push_cast
           ring)
    have hfree : adaptiveFreeStage c n s
        = adaptiveDensityC c n * FstageFinite μ w := by
      unfold adaptiveFreeStage FstageFinite
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwdef, hμdef]
      congr 1
      push_cast
      ring
    rw [hpert, hfree]
    ring
  have hRHtr : FstageFinite (perturbedEigenvalues μ hV) w
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (adaptiveN c n)))
          (perturbedResolventOp μ hV w) :=
    (perturbedResolventOp_trace μ hV w).symm
  have hRDtr : FstageFinite μ w
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (adaptiveN c n)))
          (freeResolventOpE μ w) :=
    (freeResolventOpE_trace μ w).symm
  rw [hstep1, hRHtr, hRDtr, ← map_sub,
    resolvent_sub_eq_first_plus_second μ hV w hneF hneP,
    map_add, map_neg]
  unfold decodedAdaptiveFirstOrderWindow decodedAdaptiveSecondResolventResidual
  first
    | (simp only [← hμdef, ← hVdef, ← hwdef]
       ring)
    | ring
    | (simp only [← hwdef]
       ring)

#print axioms decodedAdaptiveFirstOrderWindow
#print axioms decodedAdaptiveSecondResolventResidual
#print axioms decodedAdaptiveShortResidual
#print axioms decodedFadmPrimeStage_eq_first_plus_second

end

end RHFormalization
