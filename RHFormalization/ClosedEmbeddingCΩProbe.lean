import Mathlib
import RHFormalization.AscoliRelativelyCompactBoxed

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Topology Complex

#check DFunLike.coe
#check ContinuousMap.toFun
#check Isometry.isClosedEmbedding
#check IsClosedEmbedding
#check IsClosedMap
#check ArzelaAscoli.isCompact_of_equicontinuous

example :
    IsClosedEmbedding
      (DFunLike.coe : C((Ω : Set ℂ), ℂ) → ((Ω : Set ℂ) → ℂ)) := by
  fail_if_success
    apply Isometry.isClosedEmbedding
  -- If this goal is not immediately solvable from Mathlib, then Claude's proof line is not valid.
  -- Do not put sorry here.
  infer_instance

end
end RHFormalization
