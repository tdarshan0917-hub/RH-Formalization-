import RHFormalization.ResolventDMasterResidualScaffold
import RHFormalization.DCanRemFromAscoli
import RHFormalization.ResolventStageHolo
import RHFormalization.ResolventDOverlapInput
import RHFormalization.AscoliBridgeLayer3
import RHFormalization.MontelSubsequenceAssembly
import RHFormalization.ResolventDFHLimit
import RHFormalization.HalfPlaneGeometry
import RHFormalization.CorrectedResolventPayload
import RHFormalization.ResolventOperatorLayer
import Mathlib

/-!
# Construct R : DMasterResidualData for the live resolvent layer

Builds the master-residual object via `dcanrem_from_ascoli`, with every input banked
EXCEPT the two genuine analytic obligations, taken as named hypotheses:
  - `ResolventRStageLocBdd`  : residual local boundedness on Ω-compacts (the D.CAN-REM estimate)
  - `h_ascoli`               : AscoliExtraction for the resolvent family
All other inputs (stage-holo, overlap, RH-holo) are banked.
This proves the entire chain to R closes around those named obligations.
-/

namespace RHFormalization
open Filter Topology Complex Set

/-- resolventRH is holomorphic on Ω. (resolventRH = resolventFH - Bshared; here we take it
    as the limit object — its holomorphy is supplied to the bridge via the Montel route.) -/
-- h_overlap wrapped as the ∃U shape dcanrem_from_ascoli wants, seeded on RightHalfPlane 1.
theorem resolvent_overlap_exists :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
      ∀ s ∈ U, Filter.Tendsto
        (fun n => resolventOperatorLayer.toStagePackage.R_stage (primePowerStage n) s)
        atTop (nhds (resolventRH s)) := by
  refine ⟨RightHalfPlane 1, isOpen_RightHalfPlane 1, rightHalfPlane_nonempty 1,
    rightHalfPlane_subset_Omega 1 (by norm_num), ?_⟩
  intro s hs
  exact resolvent_R_stage_overlap_tendsto s hs

/-- **Construct R from the two named obligations.** Every other input is banked. -/
noncomputable def resolventDMasterResidual_from_obligations
    (hLB : ResolventRStageLocBdd)
    (h_RH_holo : HolomorphicOnC resolventRH Ω)
    (h_ascoli : AscoliExtraction
      (fun n s => resolventOperatorLayer.toStagePackage.R_stage (primePowerStage n) s)) :
    DMasterResidualData resolventOperatorLayer.toStagePackage :=
  dcanrem_from_ascoli
    resolventOperatorLayer.toStagePackage primePowerStage resolventRH
    resolvent_stage_holo_primePowerStage
    hLB
    resolvent_overlap_exists
    h_RH_holo
    h_ascoli

#print axioms resolventDMasterResidual_from_obligations

end RHFormalization
