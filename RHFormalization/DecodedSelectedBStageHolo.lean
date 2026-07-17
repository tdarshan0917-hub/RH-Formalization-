-- SENTINEL: decoded-selected-B-stage-holo-v1
import RHFormalization.AdmissibleRStageHolo
import RHFormalization.DecodedAdaptiveGalerkinStage
import Mathlib

/-!
# B-side of h_stage_holo along the DECODED net
UPSTREAM: galerkinStagePackage.B_stage α = finiteCanonicalPrimePowerPackage
  (activePrimePowerPairsCenterBelow α.R) shiftedLaplaceHeatKernelC — generic
  in the stage; kernel point-holo banked
  (shiftedLaplaceHeatKernelC_holomorphicAt_Omega). Donor proof: E1
  admissible_B_stage_holo (AdmissibleRStageHolo.lean), verbatim with the
  decoded stage substituted.
TARGET: ∀ c n, HolomorphicOnC (B_stage (decodedAdaptiveGalerkinStageSeq c n)) Ω.
DOWNSTREAM CONSUMER: decoded_selected_R_stage_holo = F-side − B-side →
  buildDMasterResidualDataAlong.h_stage_holo (DMasterResidualAlong.lean:24)
  at alpha = decodedAdaptiveGalerkinStageSeq c → DMasterResidualData →
  selectedOperatorResolventBridgeDirect → RH endpoint.
SEMANTIC: finite sum of weightC · shiftedLaplaceHeatKernelC(center,·);
  holomorphy per fixed n — no depth issue (Q2 clean).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- B-side, DECODED net: the finite canonical kernel package at every decoded
adaptive stage is holomorphic on Ω. -/
theorem decoded_selected_B_stage_holo (c : ℝ) (n : ℕ) :
    HolomorphicOnC
      (fun s => galerkinStagePackage.B_stage (decodedAdaptiveGalerkinStageSeq c n) s)
      Ω := by
  intro z hz
  have hsum : AnalyticAt ℂ
      (fun s =>
        (activePrimePowerPairsCenterBelow
          (decodedAdaptiveGalerkinStageSeq c n).R).sum
          (fun q => q.weightC * shiftedLaplaceHeatKernelC q.center s)) z := by
    have hterms : ∀ q ∈ activePrimePowerPairsCenterBelow
        (decodedAdaptiveGalerkinStageSeq c n).R,
        AnalyticAt ℂ
          (fun s => q.weightC * shiftedLaplaceHeatKernelC q.center s) z := by
      intro q _
      have hk := shiftedLaplaceHeatKernelC_holomorphicAt_Omega q.center hz
      first
        | exact analyticAt_const.mul hk
        | exact analyticAt_const.mul hk.analyticAt
        | exact analyticAt_const.mul hk.analyticAt_Omega
    have hpi := Finset.analyticAt_sum
      (activePrimePowerPairsCenterBelow (decodedAdaptiveGalerkinStageSeq c n).R)
      hterms
    have hfun : (∑ q ∈ activePrimePowerPairsCenterBelow
          (decodedAdaptiveGalerkinStageSeq c n).R,
        fun s => q.weightC * shiftedLaplaceHeatKernelC q.center s)
        = fun s => ∑ q ∈ activePrimePowerPairsCenterBelow
          (decodedAdaptiveGalerkinStageSeq c n).R,
          q.weightC * shiftedLaplaceHeatKernelC q.center s := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun] at hpi
    exact hpi
  have htarget : AnalyticAt ℂ
      (fun s => galerkinStagePackage.B_stage (decodedAdaptiveGalerkinStageSeq c n) s)
      z := by
    first
      | exact hsum
      | (convert hsum using 2; rfl)
  exact htarget.analyticWithinAt

#print axioms decoded_selected_B_stage_holo

end

end RHFormalization
