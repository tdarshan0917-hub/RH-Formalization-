import RHFormalization.SelectedFiniteCanonicalPayloadInstance
import RHFormalization.SelectedFiniteOperatorLayer
import RHFormalization.CanonicalPrimePowerSupportAwareExhaustion
import RHFormalization.PrimePowerDFiniteStage
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Target file for the missing selected finite-canonical limit.

This is the bridge needed for:
  L : DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer C

No RH endpoint here.
No H-side.
No new route.
-/

#check selectedFiniteOperatorLayer
#check selectedFiniteIndices
#check selectedFiniteKernel
#check selectedFiniteCanonicalPayload
#check selectedAppendixDFiniteSpikeExtractionWitness

-- Candidate alpha sequence.
#check primePowerStage
#check primePowerStage_R_tendsto_atTop

-- Candidate canonical shared package / tsum package.
#check canonicalPrimePowerPackageFromKernelTsum
#check finiteCanonical_tendsto_tsum_of_kernel_error_tendsto_zero_valid

-- Exact target type we now need.
#check DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer

/-
The next theorem must have this shape:

  selectedFiniteCanonicalLimit :
    DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer selectedDirectC

where selectedDirectC is the tsum package for selectedFiniteKernel.

The remaining proof obligations should reduce to:
  1. selected index exhaustion;
  2. kernel-error tends to zero;
  3. summability of the shared kernel.
-/

end
end RHFormalization
