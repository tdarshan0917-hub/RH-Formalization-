-- SENTINEL: decoded-combined-v1
import RHFormalization.DecodedAdaptiveGalerkinStage
import RHFormalization.AdaptiveFreeSplit
import RHFormalization.DBFFO3FMRBridge
import RHFormalization.AdaptiveCombinedFreeR
import Mathlib

/-!
# DecodedAdaptiveCombinedFreeR — the manuscript-faithful combined object
RAW-ERA FREEZE: `adaptiveCombinedFreeR` (raw code-center stage) is frozen as
scaffolding; this file is its decoded replacement per D.SPIKE-TRANSFER
(physical centers log p^m). IDENTITY ONLY — no bounds in this brick.

Objects:
  decodedFadmPrimeStage := F_stage(decoded) − adaptiveFreeStage
    (free operator is decode-independent: decoding moves only V's centers)
  decodedAdaptiveCombinedFreeR := (free − M) − R_stage(decoded)

Exact identity (Ω-free, pure algebra + rfl bridges):
  decodedCombined = DBFFO3CompensatedB − decodedFadmPrimeStage
provided B_stage(decoded) = B_stage(admissible) (cutoff/codes unchanged —
rfl bridge, guarded).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology BigOperators

/-- The decoded prime layer: everything in the decoded F-stage beyond the
density-normalized free part. -/
def decodedFadmPrimeStage (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.F_stage (decodedAdaptiveGalerkinStageSeq c n) s
    - adaptiveFreeStage c n s

/-- The decoded adaptive corrected combined object: `(free − M) − R(decoded)`. -/
def decodedAdaptiveCombinedFreeR (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (adaptiveFreeStage c n s - compensatorM n s)
    - galerkinStagePackage.R_stage (decodedAdaptiveGalerkinStageSeq c n) s

/-- R = F − B at the decoded stage (rfl bridge, guarded). -/
theorem decoded_R_stage_eq_F_sub_B (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.R_stage (decodedAdaptiveGalerkinStageSeq c n) s
      = galerkinStagePackage.F_stage (decodedAdaptiveGalerkinStageSeq c n) s
        - galerkinStagePackage.B_stage (decodedAdaptiveGalerkinStageSeq c n) s := by
  rfl

/-- B(decoded) = B(admissible): cutoff and codes are unchanged by decoding
(rfl bridge, guarded). -/
theorem decoded_B_stage_eq_admissible (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (decodedAdaptiveGalerkinStageSeq c n) s
      = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
  first
    | rfl
    | (show finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (decodedAdaptiveGalerkinStageSeq c n).R)
          shiftedLaplaceHeatKernelC s
        = finiteCanonicalPrimePowerPackage
            (activePrimePowerPairsCenterBelow (admissibleGalerkinStageSeq n).R)
            shiftedLaplaceHeatKernelC s
       rfl)

/-- **THE DECODED EXACT IDENTITY** (fixed stage, pure algebra):
`decodedCombined = CompensatedB − decodedPrimeStage`. -/
theorem decodedAdaptiveCombinedFreeR_eq (c : ℝ) (n : ℕ) (s : ℂ) :
    decodedAdaptiveCombinedFreeR c n s
      = DBFFO3CompensatedB n s - decodedFadmPrimeStage c n s := by
  unfold decodedAdaptiveCombinedFreeR decodedFadmPrimeStage DBFFO3CompensatedB
  rw [decoded_R_stage_eq_F_sub_B, decoded_B_stage_eq_admissible]
  ring

#print axioms decodedFadmPrimeStage
#print axioms decodedAdaptiveCombinedFreeR
#print axioms decoded_R_stage_eq_F_sub_B
#print axioms decoded_B_stage_eq_admissible
#print axioms decodedAdaptiveCombinedFreeR_eq

end

end RHFormalization
