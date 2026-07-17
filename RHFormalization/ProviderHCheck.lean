import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.HSideResidueArithmetic
import RHFormalization.PoleNormalForm
import RHFormalization.MainTheorem

namespace RHFormalization

-- replace X_CANDIDATE with the concrete name found by grep
-- noncomputable def H_default : ZeroPolePackageAPI :=
--   X_CANDIDATE.toZeroPolePackageAPI
--
-- noncomputable def P_default : PoleWitnessAPI H_default :=
--   X_CANDIDATE.toHSidePoleWitnessLayer.toPoleWitnessAPI

#check HMeromorphicWithGroupedPoles.toZeroPolePackageAPI
#check HMeromorphicWithGroupedPoles.toHSidePoleWitnessLayer
#check HSidePoleWitnessLayer.toPoleWitnessAPI

end RHFormalization
