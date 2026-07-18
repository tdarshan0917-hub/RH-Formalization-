import RHFormalization.SelectedTracePayloadFromStageFields
import RHFormalization.DFiniteStageOperator
import RHFormalization.DOperatorExport

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check DFiniteStage
#print DFiniteStage

-- The three exact missing provider facts from EF17:
example
    (h :
      ∀ (α : DFiniteStage), ∀ q ∈ selectedTraceActiveIndices_fromStage α,
        α.diagonalSpikeActive q) :
    True := by
  trivial

example
    (h :
      ∀ (α : DFiniteStage),
        ∀ m ∈ selectedTraceActiveIndices_fromStage α,
        ∀ n ∈ selectedTraceActiveIndices_fromStage α,
          selectedTraceToPP_fromStage α m =
            selectedTraceToPP_fromStage α n → m = n) :
    True := by
  trivial

example
    (h :
      ∀ (α : DFiniteStage), ∀ n ∈ selectedTraceActiveIndices_fromStage α,
        α.canonicalSpikeContribution n =
          (selectedTraceToPP_fromStage α n).weightC) :
    True := by
  trivial

-- Searchable names if they exist:
#check DFiniteStage.diagonalSpikeActive
#check DFiniteStage.diagonalSpikeActiveIndices
#check DFiniteStage.diagonalSpikeToPP
#check DFiniteStage.diagonalSpikeContribution
#check DFiniteStage.canonicalSpikeContribution

end

end RHFormalization
