-- SENTINEL: dmr-overlap-ledger-v1
import RHFormalization.DMROmegaCoreMontel
import Mathlib

/-! # B2: the overlap ledger.
On `Re s > 0`: `R_stage = galOmegaCore − canonicalPackageTail(spikeT0)`.
The Ω-continued core equals the residual plus the arithmetic tail on the
overlap — the identity the Montel/identity-theorem transfer runs through. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set
open scoped BigOperators Classical

/-- **B2: THE OVERLAP LEDGER.** -/
theorem R_stage_eq_core_sub_packageTail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = galOmegaCore n s
        - canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
            spikeT0 s := by
  rw [R_stage_eq_head_add_tail n s hs,
    galTail_eq_Ftail_sub_Btail n s hs,
    ← galFTailClosed_eq_integral n s hs]
  unfold galOmegaCore
  ring

/-- Equivalent form: the Ω-core equals residual plus arithmetic tail on
the overlap. -/
theorem core_eq_R_stage_add_packageTail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galOmegaCore n s
      = galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        + canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
            spikeT0 s := by
  rw [R_stage_eq_core_sub_packageTail n s hs]
  ring

#print axioms R_stage_eq_core_sub_packageTail
#print axioms core_eq_R_stage_add_packageTail

end

end RHFormalization
