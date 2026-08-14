import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.SeamCoreFactoredForm
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# CfBridgeIdentity — PHASE 1: the free bridge IS the arithmetic bracket

Exact, every s, no estimates. From the banked route-lock (×2):
  2·FreePaired − M = (B_stage(adaptive) − M) − 2·BcorrWin_ad + 2·defect.
The GATE chain's open constant Cf bounds the LHS; defect and BcorrWin are
certified-bounded; hence Cf-content = compensated-B-content exactly.
Consumer: PHASE 2 (partial summation ⇒ ψ-equivalence, paper first).
-/

/-- **PHASE 1 BRIDGE (exact)**: the free bridge equals the compensated
B_stage plus certified-bounded corrections. -/
theorem Cf_eq_compensatedB_add_corrections (c : ℝ) (n : ℕ) (s : ℂ) :
    2 * adaptiveFreePairedTransform c n s - compensatorM n s
      = (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
          - compensatorM n s)
        - 2 * adaptiveBcorrWin c n s
        + 2 * adaptiveGalerkinTransformDefect c n s := by
  have h := adaptiveFreePairedTransform_route_lock c n s
  rw [h]
  ring

#print axioms Cf_eq_compensatedB_add_corrections

end

end RHFormalization
