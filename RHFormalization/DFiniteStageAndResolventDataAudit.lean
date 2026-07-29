import RHFormalization.CorrectedResolventPayload
import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.DirichletPWQOModel

namespace RHFormalization
noncomputable section

#check DFiniteStage
#print DFiniteStage

#check concreteDirichletPWQOData
#print concreteDirichletPWQOData
#print axioms concreteDirichletPWQOData

#check DirichletPWQOData
#print DirichletPWQOData

#check concreteDirichletPWQOData.lamShifted
#check concreteDirichletPWQOData.toOperatorEigenvalueData
#print axioms concreteDirichletPWQOData.toOperatorEigenvalueData

#check spectralResolventPartial
#print spectralResolventPartial

#check resolventIndices
#print resolventIndices

end
end RHFormalization
