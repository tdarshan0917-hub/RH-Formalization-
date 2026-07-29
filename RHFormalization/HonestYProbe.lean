import RHFormalization.HonestYZeroResidualFromFHcan
import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.DirichletPWQOToOperatorEigenvalue

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- Probe: build the honest Y with FH = FHcan (the resolvent transform),
    using the concrete Dirichlet spectrum. Leaves S (envelope) and the
    convergence as the two open goals — Lean will print exactly what they are. -/
def honestY_probe : DDetailedConstructionWithOperatorLegality :=
  buildHonestYZeroResidualFromFHcan
    ?S
    concreteDirichletPWQOData.toOperatorEigenvalueData
    ?h_conv

end
end RHFormalization
