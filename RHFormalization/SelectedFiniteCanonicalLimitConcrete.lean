import RHFormalization.SelectedFiniteKernelError
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Concrete selected finite-canonical limit.

This is the actual selected L-provider:

  L : DOperatorFiniteCanonicalLimitAtOverlapData
        selectedFiniteOperatorLayer
        selectedDirectC

It plugs the three closed inputs:
  hmem, hsummable, herror.
-/
noncomputable def selectedFiniteCanonicalLimitConcrete :
    DOperatorFiniteCanonicalLimitAtOverlapData
      selectedFiniteOperatorLayer
      selectedDirectC :=
  buildSelectedFiniteCanonicalLimit
    selectedFiniteIndices_eventually_contains_valid
    selectedFiniteKernel_hsummable
    selectedFiniteKernel_herror

#print axioms selectedFiniteCanonicalLimitConcrete

end
end RHFormalization
