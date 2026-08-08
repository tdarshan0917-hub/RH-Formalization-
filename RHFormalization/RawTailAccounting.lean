import RHFormalization.CanonicalTailObstructionBridge
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# RawTailAccounting — raw manuscript coordinates only. No Bcorr,
no compensatorM, no seamCore, no endpoint. Audit certificate for the
manuscript's own residual: R = head + (Ftail − Btail).
-/

/-- **RAW ACCOUNTING (exact, Re s > 0)**: the manuscript's residual is the
short-time head plus the compensated large-time tail `Ftail − Btail`. -/
theorem raw_R_stage_tail_accounting (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = galHead n s + (galFTailClosed n s - galBTail n s) := by
  rw [R_stage_eq_head_add_tail n s hs]
  have h2 := galTail_eq_Ftail_sub_Btail n s hs
  have h3 := galFTailClosed_eq_integral n s hs
  have hBT : galBTail n s
      = canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
          spikeT0 s := by
    first
      | exact galB_tail_eq_canonicalPackageTail n s hs
      | rfl
  rw [h2, ← h3, hBT]

#print axioms raw_R_stage_tail_accounting

end

end RHFormalization
