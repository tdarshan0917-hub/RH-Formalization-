import RHFormalization.RealPrimeModelCorrectedProviderPlug
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
D-only capstone target.

Purpose:
  Freeze the H/model-corrected side and expose only the real-prime D/operator
  inputs still needed for the final RH call.

Do not use selectedFiniteOperatorLayer.
Do not use resolventOperatorLayer.
Do not build another endpoint route.
-/

#check realPrime_RH_model_corrected
#check h_real_zero_free
#check defaultZetaZeroFacts_of_realZeroFree h_real_zero_free
#check defaultZeroExhaustion
#check defaultZeroMultiplicityData
#check ZpoleRepSeries defaultZeroMultiplicityData
#check modelRepCorrectedHarchPackage
#check modelRepCorrectedHarchPackage_split
#check buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional
#check buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData
  (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional)
#check buildZpoleMeromorphicFromSeriesAPI
#check h_pp_from_convergence
#check buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair

/-
After this #check surface, the next theorem should have ONLY these live D-side
inputs:

  μ
  S
  FH RH
  h_FH_holo h_RH_holo
  h_F_stage_to_FH h_R_stage_to_RH
  h_R_stage_bound hσ
  hYC

Everything else should be plugged from the default/model-corrected H side.
-/

end
end RHFormalization
