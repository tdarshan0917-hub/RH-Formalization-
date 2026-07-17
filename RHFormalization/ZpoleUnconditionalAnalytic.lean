/-
Unconditional Zpole regular-point analyticity:
envelope (pillar b) → convergence API → AnalyticAt at non-pole points of Ω.
This is the ZpoleSeries half of the pillar-(c) regular case.
-/
import RHFormalization.HsumUnconditional
import RHFormalization.MeromorphyAssembly

namespace RHFormalization

noncomputable section

/-- The convergence API for the canonical zero-pole series, NO hypotheses. -/
noncomputable def unconditionalZeroPoleConvergence :
    ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
      defaultZeroExhaustion (ZpoleSeries defaultZeroMultiplicityData) :=
  buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData
    unconditionalZeroPoleEnvelope

/-- Zpole is analytic at every non-pole point of Ω — unconditional. -/
theorem zpoleSeries_analyticAt_nonpole_unconditional
    {x : ℂ} (hxΩ : x ∈ Ω) (hx : x ∉ ZeroPoleSet) :
    AnalyticAt ℂ (ZpoleSeries defaultZeroMultiplicityData) x :=
  zpole_analyticAt_nonpole defaultZeroMultiplicityData
    (ZpoleSeries defaultZeroMultiplicityData)
    unconditionalZeroPoleConvergence x hxΩ hx

#print axioms unconditionalZeroPoleConvergence
#print axioms zpoleSeries_analyticAt_nonpole_unconditional

end

end RHFormalization
