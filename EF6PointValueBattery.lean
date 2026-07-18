import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.HExplicitFormulaWitnessCancellation
import RHFormalization.HExplicitFormulaLocalCancellation
import RHFormalization.AnalyticWrappers

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#print LocalEqAtC
#print HasPrincipalPartAtC
#check Harch_local_extension_at_witness_from_cancelled_principal_parts
#check holomorphicAtC_congr
#check AnalyticAt.congr
#check Filter.EventuallyEq.filter_mono
#check nhdsWithin
#check Function.update

-- This is just a shape probe: can we even formulate the punctured version cleanly?
example
    (f g h : ℂ → ℂ) (z : ℂ)
    (hh : HolomorphicAtC h z)
    (heq : ∀ᶠ w in 𝓝[≠] z, h w = f w + g w) :
    True := by
  trivial

end

end RHFormalization
