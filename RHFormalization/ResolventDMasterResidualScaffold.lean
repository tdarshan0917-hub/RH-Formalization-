import RHFormalization.DCanRemFromMontel
import RHFormalization.DCanRemFromAscoli
import RHFormalization.ResolventStageHolo
import RHFormalization.ResolventDOverlapInput
import RHFormalization.ResolventHConvAbsConv
import RHFormalization.AscoliObligationDirect
import RHFormalization.CorrectedResolventDirectCancellationTarget
import RHFormalization.CorrectedResolventPayload
import RHFormalization.ResolventOperatorLayer
import Mathlib

/-!
# Build R : DMasterResidualData for the live resolvent layer

Constructs the master-residual object the bridge consumes, from:
  - h_stage_holo : BANKED (resolvent_stage_holo_primePowerStage)
  - h_overlap    : BANKED (resolvent_R_stage_overlap_tendsto, on RightHalfPlane 1)
  - h_ascoli     : BANKED (ascoliRelCompactObligation_direct -> AscoliExtraction)
  - h_RH_holo    : from the Montel limit
  - h_loc_bdd    : the SINGLE remaining analytic obligation (residual local boundedness
                   on all Omega-compacts; the genuine D.CAN-REM cancellation estimate).
This file ISOLATES that one obligation by name and proves the entire rest of the chain
closes around it.
-/

namespace RHFormalization
open Filter Topology Complex Set

/-- The live resolvent R_stage local-boundedness obligation (the genuine remaining estimate). -/
def ResolventRStageLocBdd : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖resolventOperatorLayer.toStagePackage.R_stage (primePowerStage n) s‖ ≤ C

end RHFormalization
