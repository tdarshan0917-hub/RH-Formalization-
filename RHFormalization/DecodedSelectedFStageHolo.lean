-- SENTINEL: decoded-selected-F-stage-holo-v1
import RHFormalization.DecodedEigenvalueFloor
import RHFormalization.DecodedGalerkinPerturbedFStage
import RHFormalization.DecodedAdaptiveGalerkinStage
import Mathlib

/-!
# F-side of h_stage_holo along the DECODED net
UPSTREAM: decodedEigenvalue_nonneg (floor, this session) +
  perturbedFStage_shift_eq + FstageFinite_holo_on_Omega (generic donors) +
  decodedAdaptiveGalerkinStageSeq_F_stage (rfl bridge: density × shifted F).
  Donor proof: admissibleShiftedFStage_holo +
  galerkinStagePackage_F_stage_holo_admissible (S1/D1), ported verbatim.
TARGET: ∀ c n, HolomorphicOnC (F_stage (decodedAdaptiveGalerkinStageSeq c n)) Ω.
DOWNSTREAM CONSUMER: decoded_selected_R_stage_holo →
  buildDMasterResidualDataAlong.h_stage_holo (DMasterResidualAlong.lean:24).
SEMANTIC: shift moves an already-nonneg decoded spectrum right; density
  factor via const_mul. δ = 1, ppWeightReal, decoded centers, live net.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Ω-holomorphy of the SHIFTED decoded F-trace. -/
theorem decodedShiftedFStage_holo
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (μ : Fin N → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) :
    HolomorphicOnC
      (fun s =>
        decodedGalerkinPerturbedFStage (N := N) μ 1 qs ppWeightReal L
          (s + (SupVConst : ℂ))) Ω := by
  have heq :
      (fun s =>
          decodedGalerkinPerturbedFStage (N := N) μ 1 qs ppWeightReal L
            (s + (SupVConst : ℂ)))
        = FstageFinite (fun i =>
            perturbedEigenvalues μ
              (decodedGalerkinVC_isHermitian (N := N) 1 qs ppWeightReal L) i
              + SupVConst) := by
    funext s
    exact perturbedFStage_shift_eq μ
      (decodedGalerkinVC_isHermitian (N := N) 1 qs ppWeightReal L) SupVConst s
  rw [heq]
  refine FstageFinite_holo_on_Omega _ (fun i => ?_)
  have h1 := decodedEigenvalue_nonneg L hL qs μ hμ i
  have h2 := SupVConst_nonneg_adm
  linarith

/-- **h_stage_holo, F-side, DECODED NET**: the package F-slot at every decoded
adaptive stage is holomorphic on Ω. -/
theorem decoded_selected_F_stage_holo (c : ℝ) (n : ℕ) :
    HolomorphicOnC
      (fun s =>
        galerkinStagePackage.F_stage (decodedAdaptiveGalerkinStageSeq c n) s) Ω := by
  have hμnn : ∀ k, 0 ≤ galerkinFreeMu (adaptiveN c n) (adaptiveL c n) k := by
    intro k
    first
      | exact galerkinFreeMu_nonneg _ _ k
      | (unfold galerkinFreeMu; positivity)
      | exact sq_nonneg _
  have h := decodedShiftedFStage_holo (adaptiveL c n) (adaptiveL_pos c n)
    (activePrimePowerCodesCenterBelow (admR n))
    (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) hμnn
  have heq : (fun s =>
      galerkinStagePackage.F_stage (decodedAdaptiveGalerkinStageSeq c n) s)
      = fun s => adaptiveDensityC c n *
          decodedGalerkinPerturbedFStage (N := adaptiveN c n)
            (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (adaptiveL c n) (s + (SupVConst : ℂ)) := by
    funext s
    first
      | exact decodedAdaptiveGalerkinStageSeq_F_stage c n s
      | rfl
  rw [heq]
  first
    | exact analyticOn_const.mul h
    | exact (show AnalyticOn ℂ (fun _ : ℂ => adaptiveDensityC c n) Ω from
        analyticOn_const).mul h
    | exact h.const_mul (adaptiveDensityC c n)
    | exact AnalyticOn.mul analyticOn_const h

#print axioms decodedShiftedFStage_holo
#print axioms decoded_selected_F_stage_holo

end

end RHFormalization
