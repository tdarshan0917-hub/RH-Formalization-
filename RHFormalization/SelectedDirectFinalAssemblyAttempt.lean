import RHFormalization.SelectedDirectDEndgame
import RHFormalization.XiSummability
import RHFormalization.EtaPositivity
import RHFormalization.FinalSpineFromRealZeroFree
import RHFormalization.DefaultZetaZeroFacts
import RHFormalization.DefaultZeroExhaustion
import RHFormalization.ZpoleFromSeries
import RHFormalization.EnvelopeFromZeroDensity
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Final selected-direct assembly attempt.

This is the ONLY active target now:

  RH_from_selected_direct_D_final_inputs

No FinalRHAssembly.
No clean-Laplace bridge.
No realPrimeY-vs-DBcan comparison.
No broad search.
-/

#check RH_from_selected_direct_D_final_inputs

-- D-side final bridge constructor already used by the theorem.
#check selectedOperatorResolventBridgeDirect_from_final_D_inputs

-- Real-zero-free input.
#check h_real_zero_free

-- Zero/H-side standard providers.
#check defaultZeroMultiplicityData
#check defaultZeroExhaustion
#check ZpoleSeries defaultZeroMultiplicityData
#check hsum_unconditional
#check buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional
#check buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData
  (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional)
#check h_pp_from_convergence
#check meromorphicOn_from_convergence

-- API-level endpoint expected by selected direct theorem.
#check ZeroPolePackageAPI
#check InterfaceBridgeAPI
#check PoleWitnessAPI
#check RigidityNoPoleAPI

end
end RHFormalization
