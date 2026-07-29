import RHFormalization.ShiftedLaplaceAbsConvMTest

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check ShiftedLaplaceWitnessCancellationData
#check WitnessCancellationData
#check shiftedLaplace_witness_extensions_from_cancellation_data
#check shiftedLaplace_holo_from_cancellation_and_regular
#check shiftedLaplace_holo_from_cancellation_zeroDensity_localMTest

example (sigma0 : ℝ) :
    (∀ W : ZeroWitness,
      ShiftedLaplaceWitnessCancellationData sigma0 W) →
    True := by
  intro hcancel
  trivial

end

end RHFormalization
