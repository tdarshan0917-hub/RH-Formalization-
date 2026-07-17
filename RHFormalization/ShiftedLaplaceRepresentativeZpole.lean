import RHFormalization.HMeromorphicPackage
import RHFormalization.ShiftedLaplaceBppFromBridge
import RHFormalization.ShiftedLaplaceZpoleWiring

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem zeroPoleSummand_principalPart_at_polePoint
    (M : ZeroMultiplicityData) (ρ : ℂ) :
    HasPrincipalPartAtC
      (fun s => zeroPoleSummand M ρ s)
      (polePoint ρ)
      (M.mult ρ : ℂ) := by
  refine ⟨fun _ => 0, analyticAt_const, ?_⟩
  filter_upwards [] with w hwne
  unfold zeroPoleSummand zeroPoleDenom polePoint
  have hden : w + ρ * (1 - ρ) = w - (-(ρ * (1 - ρ))) := by ring
  rw [hden]
  ring

#print axioms zeroPoleSummand_principalPart_at_polePoint

end
end RHFormalization
