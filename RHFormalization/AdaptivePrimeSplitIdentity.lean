import RHFormalization.AdaptivePrimeSplitObjects
import RHFormalization.AdmissiblePrimeStageIdentity
import Mathlib

/-!
# AdaptivePrimeSplitIdentity — exact prime-layer split on the adaptive net

Mirror of `FadmPrimeStage_eq_trace_diff` and
`FadmPrimeStage_eq_first_plus_second` at the adaptive parameters. All the
heavy lemmas consumed (`resolvent_sub_eq_first_plus_second`,
`perturbedFStage_shift_eq`, `FstageFinite_comm_shift`,
`admissibleEigenvalue_nonneg`, trace representations) are generic in
`(N, μ, hV, L)` and instantiate directly.

Endpoint: `adaptiveFadmPrimeStage = adaptiveFirstOrderWindow +
adaptiveSecondResolventResidual` on Ω — the exact bookkeeping the adaptive
FMR bridge consumes. The D.LOC analysis then bounds the second piece via
`adaptiveGalerkinStage_DADM`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- The perturbed spectrum at the adaptive stage. -/
def adaptivePerturbedLam (c : ℝ) (n : ℕ) : Fin (adaptiveN c n) → ℝ :=
  fun i => perturbedEigenvalues (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
    (galerkinVC_isHermitian (N := adaptiveN c n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
      (adaptiveL c n)) i

/-- The adaptive free stage is the free finite trace at the commuted shift. -/
theorem adaptiveFreeStage_eq_FstageFinite (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveFreeStage c n s
      = adaptiveDensityC c n *
          FstageFinite (fun i : Fin (adaptiveN c n) =>
            SupVConst + galerkinFreeMu (adaptiveN c n) (adaptiveL c n) i) s := by
  unfold adaptiveFreeStage FstageFinite
  rfl

/-- **Adaptive trace-diff representation** (mirror of
`FadmPrimeStage_eq_trace_diff`). -/
theorem adaptiveFadmPrimeStage_eq_trace_diff (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveFadmPrimeStage c n s
      = adaptiveDensityC c n *
          (FstageFinite (fun i => adaptivePerturbedLam c n i + SupVConst) s
            - FstageFinite (fun i : Fin (adaptiveN c n) =>
                SupVConst + galerkinFreeMu (adaptiveN c n) (adaptiveL c n) i) s) := by
  unfold adaptiveFadmPrimeStage
  rw [adaptiveGalerkinStageSeq_F_stage c n s,
    adaptiveFreeStage_eq_FstageFinite c n s]
  have hshift : galerkinPerturbedFStage (N := adaptiveN c n)
      (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
      (adaptiveL c n) (s + (SupVConst : ℂ))
      = FstageFinite (fun i => adaptivePerturbedLam c n i + SupVConst) s := by
    unfold adaptivePerturbedLam
    exact perturbedFStage_shift_eq (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
      (galerkinVC_isHermitian (N := adaptiveN c n) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
        (adaptiveL c n)) SupVConst s
  rw [hshift]
  ring

/-- **BRICK: the adaptive manuscript-faithful split.**
`adaptivePrime = adaptiveFirstOrderWindow + adaptiveSecondResolventResidual`
on Ω. -/
theorem adaptiveFadmPrimeStage_eq_first_plus_second
    (c : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    adaptiveFadmPrimeStage c n s
      = adaptiveFirstOrderWindow c n s
        + adaptiveSecondResolventResidual c n s := by
  set μ := galerkinFreeMu (adaptiveN c n) (adaptiveL c n) with hμdef
  set hV := galerkinVC_isHermitian (N := adaptiveN c n) 1
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
      have h := admissibleEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n)
        (activePrimePowerCodesCenterBelow (admR n)) μ hμnn i
      first
        | exact h
        | (rw [hVdef]; exact h)
    have hcast : w + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)
        = s + ((SupVConst + perturbedEigenvalues μ hV i : ℝ) : ℂ) := by
      rw [hwdef]; push_cast; ring
    rw [hcast]
    exact add_real_ne_zero_of_mem_Omega hs
      (add_nonneg SupVConst_nonneg_adm hlamnn)
  have hstep1 : adaptiveFadmPrimeStage c n s
      = adaptiveDensityC c n *
          (FstageFinite (perturbedEigenvalues μ hV) w - FstageFinite μ w) := by
    rw [adaptiveFadmPrimeStage_eq_trace_diff c n s]
    have e1 : FstageFinite (fun i => adaptivePerturbedLam c n i + SupVConst) s
        = FstageFinite (perturbedEigenvalues μ hV) w := by
      rw [FstageFinite_shift (adaptivePerturbedLam c n) SupVConst s]
      first
        | rfl
        | (unfold adaptivePerturbedLam; rw [hμdef, hVdef, hwdef])
        | (congr 1)
    have e2 : FstageFinite
          (fun i : Fin (adaptiveN c n) =>
            SupVConst + galerkinFreeMu (adaptiveN c n) (adaptiveL c n) i) s
        = FstageFinite μ w := by
      rw [FstageFinite_comm_shift (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
        SupVConst s]
    rw [e1, e2]
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
  unfold adaptiveFirstOrderWindow adaptiveSecondResolventResidual
  first
    | ring
    | (rw [← hμdef, ← hwdef]; ring)
    | (rw [← hμdef]; ring)
    | (push_cast; ring)
    | rfl

/-- Restatement with the assembled short residual (FMR shape). -/
theorem adaptiveFadmPrimeStage_eq_shortResidual
    (c : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    adaptiveFadmPrimeStage c n s = adaptiveShortResidual c n s := by
  rw [adaptiveFadmPrimeStage_eq_first_plus_second c n hs]
  rfl

#print axioms adaptiveFadmPrimeStage_eq_trace_diff
#print axioms adaptiveFadmPrimeStage_eq_first_plus_second
#print axioms adaptiveFadmPrimeStage_eq_shortResidual

end

end RHFormalization
