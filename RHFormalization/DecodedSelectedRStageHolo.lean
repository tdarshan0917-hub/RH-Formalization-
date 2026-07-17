-- SENTINEL: decoded-selected-R-stage-holo-v4
import RHFormalization.DecodedSelectedFStageHolo
import RHFormalization.DecodedSelectedBStageHolo
import RHFormalization.DMasterResidualAlong
import Mathlib

/-!
# h_stage_holo along the DECODED net (F − B subtraction)
UPSTREAM: decoded_selected_F_stage_holo + decoded_selected_B_stage_holo
  (both this session). Donor: admissible_R_stage_holo (E1), verbatim.
TARGET: ∀ n, HolomorphicOnC (R_stage (decodedAdaptiveGalerkinStageSeq c n)) Ω.
DOWNSTREAM CONSUMER: buildDMasterResidualDataAlong.h_stage_holo
  (DMasterResidualAlong.lean:24) at alpha = decodedAdaptiveGalerkinStageSeq c
  → DMasterResidualData → selectedOperatorResolventBridgeDirect → RH endpoint.
SEMANTIC: definitional split; difference of Ω-holomorphic functions.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- **h_stage_holo along the DECODED net** — first of the two inputs to
`buildDMasterResidualDataAlong` at the live alpha. -/
theorem decoded_selected_R_stage_holo (c : ℝ) (n : ℕ) :
    HolomorphicOnC
      (fun s =>
        galerkinStagePackage.R_stage (decodedAdaptiveGalerkinStageSeq c n) s) Ω := by
  intro z hz
  have hF := decoded_selected_F_stage_holo c n z hz
  have hB := decoded_selected_B_stage_holo c n z hz
  first
    | exact hF.sub hB
    | exact AnalyticWithinAt.sub hF hB

#print axioms decoded_selected_R_stage_holo

end

end RHFormalization
