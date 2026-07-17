-- SENTINEL: admissible-R-stage-holo-v4
import RHFormalization.GalerkinFStageUniformBound
import RHFormalization.AdaptiveDefectHolo
import RHFormalization.DMasterResidualAlong
import Mathlib

/-!
# h_stage_holo along the admissible net
UPSTREAM: R_stage(α) = α.appendixDFiniteFStage(s+SupVConst) − finite kernel
  package. F-side: galerkinStagePackage_F_stage_holo_admissible (banked).
  B-side: finite sum of weightC · shiftedLaplaceHeatKernelC(center, ·); kernel
  point-holo banked (shiftedLaplaceHeatKernelC_holomorphicAt_Omega).
TARGET: ∀ n, HolomorphicOnC (fun s => R_stage(admissibleGalerkinStageSeq n) s) Ω.
DOWNSTREAM CONSUMER: buildDMasterResidualDataAlong.h_stage_holo with
  alpha = admissibleGalerkinStageSeq → DMasterResidualData → RH_from_admissible_R.
SEMANTIC: definitional split; difference of Ω-holomorphic functions.
NOTE (pin fact): HolomorphicOnC unfolds per-point to AnalyticWithinAt ℂ f Ω z.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- B-side: the finite canonical kernel package is holomorphic on Ω. -/
theorem admissible_B_stage_holo (n : ℕ) :
    HolomorphicOnC
      (fun s => galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
      Ω := by
  intro z hz
  have hsum : AnalyticAt ℂ
      (fun s =>
        (activePrimePowerPairsCenterBelow
          (admissibleGalerkinStageSeq n).R).sum
          (fun q => q.weightC * shiftedLaplaceHeatKernelC q.center s)) z := by
    have hterms : ∀ q ∈ activePrimePowerPairsCenterBelow
        (admissibleGalerkinStageSeq n).R,
        AnalyticAt ℂ
          (fun s => q.weightC * shiftedLaplaceHeatKernelC q.center s) z := by
      intro q _
      have hk := shiftedLaplaceHeatKernelC_holomorphicAt_Omega q.center hz
      first
        | exact analyticAt_const.mul hk
        | exact analyticAt_const.mul hk.analyticAt
        | exact analyticAt_const.mul hk.analyticAt_Omega
    have hpi := Finset.analyticAt_sum
      (activePrimePowerPairsCenterBelow (admissibleGalerkinStageSeq n).R)
      hterms
    have hfun : (∑ q ∈ activePrimePowerPairsCenterBelow
          (admissibleGalerkinStageSeq n).R,
        fun s => q.weightC * shiftedLaplaceHeatKernelC q.center s)
        = fun s => ∑ q ∈ activePrimePowerPairsCenterBelow
          (admissibleGalerkinStageSeq n).R,
          q.weightC * shiftedLaplaceHeatKernelC q.center s := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun] at hpi
    exact hpi
  have htarget : AnalyticAt ℂ
      (fun s => galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
      z := by
    first
      | exact hsum
      | (convert hsum using 2; rfl)
  exact htarget.analyticWithinAt

/-- **h_stage_holo along the admissible net** — first of the two inputs to
`buildDMasterResidualDataAlong`. -/
theorem admissible_R_stage_holo (n : ℕ) :
    HolomorphicOnC
      (fun s => galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
      Ω := by
  intro z hz
  have hF := galerkinStagePackage_F_stage_holo_admissible n z hz
  have hB := admissible_B_stage_holo n z hz
  first
    | exact hF.sub hB
    | exact AnalyticWithinAt.sub hF hB

#print axioms admissible_B_stage_holo
#print axioms admissible_R_stage_holo

end

end RHFormalization
