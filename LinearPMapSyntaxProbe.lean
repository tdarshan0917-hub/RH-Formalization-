import RHFormalization.DNativeUnboundedOperator
import Mathlib

namespace RHFormalization

variable {E : Type}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℂ E]
variable [CompleteSpace E]

variable (T : E →ₗ.[ℂ] E)

#check T.domain
#check (T.domain : Set E)
#check fun (x : T.domain) => (x : E)

-- Application syntax probes:
#check fun (x : T.domain) => T x
#check fun (x : T.domain) => T (x : E)
#check fun (x : E) (hx : x ∈ T.domain) => T x hx

-- Constructor / projection probes:
#check LinearPMap
#check LinearPMap.adjoint
#check LinearPMap.IsClosed

end RHFormalization
