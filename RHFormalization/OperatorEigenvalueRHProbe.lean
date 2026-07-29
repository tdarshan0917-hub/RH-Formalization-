import RHFormalization.OperatorEigenvalueData
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.DOperatorExport

namespace RHFormalization
noncomputable section
open Complex

#check @OperatorEigenvalueData.FHcan_holo
#check @RH_from_designed_D_zero_density
#check @DMasterResidualData
#check @DResidualSectorBoundsAPI

theorem operatorEigenvalueData_probe
    (E : OperatorEigenvalueData) :
    RiemannHypothesis := by
  trace_state
  fail

end
end RHFormalization
