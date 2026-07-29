import RHFormalization.ResolventOperatorLayer
import RHFormalization.HonestYFromFHcan
import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.DirichletPWQOToOperatorEigenvalue

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- Probe: honest Y over the RESOLVENT layer (not designed), via the general
    builder. Leaves the real inputs as holes so Lean prints exactly what is
    needed. -/
def honestY_resolvent_probe : DDetailedConstructionWithOperatorLegality :=
  buildHonestYFromFHcan
    resolventOperatorLayer
    ?S
    concreteDirichletPWQOData.toOperatorEigenvalueData
    ?RH
    ?h_RH_holo
    ?h_F_stage_to_FHcan
    ?h_R_stage_to_RH
    ?h_R_stage_bound
    ?hsigma

end
end RHFormalization
