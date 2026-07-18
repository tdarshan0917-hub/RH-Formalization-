import RHFormalization.SelectedOperatorLayerFromStageFields
import RHFormalization.DesignedOperatorLayer

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check selectedFiniteOperatorLayer_fromStageFields
#check designedFiniteOperatorLayer

#print selectedFiniteOperatorLayer_fromStageFields
#print designedFiniteOperatorLayer

-- Compare the stage package fields.
#check selectedFiniteOperatorLayer_fromStageFields.toStagePackage
#check designedFiniteOperatorLayer.toStagePackage

#check selectedFiniteOperatorLayer_fromStageFields.toStagePackage.F_stage
#check designedFiniteOperatorLayer.toStagePackage.F_stage

#check selectedFiniteOperatorLayer_fromStageFields.toStagePackage.B_stage
#check designedFiniteOperatorLayer.toStagePackage.B_stage

#check selectedFiniteOperatorLayer_fromStageFields.toStagePackage.R_stage
#check designedFiniteOperatorLayer.toStagePackage.R_stage

#check selectedFiniteOperatorLayer_fromStageFields.toStagePackage.sigma0
#check designedFiniteOperatorLayer.toStagePackage.sigma0

-- Hard equality probes. These are allowed to fail; the errors tell us where the layers diverge.
example :
    selectedFiniteOperatorLayer_fromStageFields.toStagePackage.F_stage =
      designedFiniteOperatorLayer.toStagePackage.F_stage := by
  rfl

example :
    selectedFiniteOperatorLayer_fromStageFields.toStagePackage.B_stage =
      designedFiniteOperatorLayer.toStagePackage.B_stage := by
  rfl

example :
    selectedFiniteOperatorLayer_fromStageFields.toStagePackage.R_stage =
      designedFiniteOperatorLayer.toStagePackage.R_stage := by
  rfl

example :
    selectedFiniteOperatorLayer_fromStageFields.toStagePackage.sigma0 =
      designedFiniteOperatorLayer.toStagePackage.sigma0 := by
  rfl

end

end RHFormalization
