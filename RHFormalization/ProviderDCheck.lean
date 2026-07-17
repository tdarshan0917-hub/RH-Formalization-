import RHFormalization.DesignedDetailedConstruction
import RHFormalization.MainTheorem

namespace RHFormalization

noncomputable def D_default : OperatorResolventBridge :=
  designedY.toOperatorResolventBridge

#check designedY
#check D_default
#print axioms designedY
#print axioms D_default

end RHFormalization
