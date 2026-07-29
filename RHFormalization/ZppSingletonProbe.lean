import RHFormalization.HPPEndgame
import RHFormalization.ShiftedLaplaceZpoleWiring

namespace RHFormalization
noncomputable section
open Complex

example (W : ZeroWitness) :
    groupedResidueCoeff defaultZeroMultiplicityData
        (defaultGroupedPoleClass defaultZeroMultiplicityData W)
      = groupedResidueCoeff defaultZeroMultiplicityData
        (pairGroupedPoleClass defaultZeroMultiplicityData W) := by
  unfold groupedResidueCoeff
  simp only [defaultGroupedPoleClass, pairGroupedPoleClass]
  sorry

end
end RHFormalization
