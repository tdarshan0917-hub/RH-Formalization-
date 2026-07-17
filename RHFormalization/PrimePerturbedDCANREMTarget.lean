import RHFormalization.PrimePerturbedPayloadAligned
import RHFormalization.DResidualBulkSectorHelpers
import RHFormalization.DResidualSectorToRStageBound
import RHFormalization.RStageBoundAttack
import RHFormalization.DispMajorantSuperpoly
import RHFormalization.DispTransformBounded
import RHFormalization.AnchorFinite
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- Abstract exact shape of the real remaining D.CAN-REM bound. -/
def AllOmegaRStageBoundForPayload
    (P : SelectedFiniteCanonicalPayload) : Prop :=
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖P.R_stage α s‖ ≤ C

/-- The real target specialized to the aligned prime-perturbed payload. -/
def PrimePerturbedAlignedAllOmegaRStageBound
    {N : ℕ} (μ : Fin N → ℝ) : Prop :=
  AllOmegaRStageBoundForPayload (primePerturbedPayloadAligned μ)

#check residualBulkSectorBoundsAPI_of_R_stage_bound
#check R_stage_bound_of_sector_bounds
#check StageRBound_of_split
#check disp_majorant_superpoly
#check disp_transform_bounded
#check anchor_integrand_integrable
#check anchor_admissible

#print axioms PrimePerturbedAlignedAllOmegaRStageBound

end
end RHFormalization
