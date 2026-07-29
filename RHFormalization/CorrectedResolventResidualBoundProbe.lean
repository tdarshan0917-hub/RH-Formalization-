import RHFormalization.CorrectedResolventPayload
import RHFormalization.DOperatorExport
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/--
This is the real Approach-B theorem:
spectral resolvent partial sum minus finite prime package is uniformly bounded
on Ω-compacts.
-/
theorem correctedResolventPayload_R_stage_bound :
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖correctedResolventPayload.R_stage α s‖ ≤ C := by
  intro K hK hKOmega
  unfold correctedResolventPayload
  unfold spectralResolventPartial
  trace_state
  fail

end
end RHFormalization
