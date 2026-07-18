import RHFormalization.OmegaTopology
import RHFormalization.GlobalMeromorphicIdentity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Star

namespace RHFormalization

noncomputable section

open Complex Set

#check StarConvex
#check StarConvex.isPreconnected
#check StarConvex.isPathConnected
#check starConvex_iff
#check segment
#check lineMap
#check Convex.isPreconnected
#check IsPathConnected.isPreconnected

/--
Shape probe only. This records the likely direct route:
prove Ω is star-convex from basepoint 1, then derive preconnectedness.
-/
example :
    StarConvex ℝ (1 : ℂ) Ω →
    IsPreconnected Ω := by
  intro hstar
  -- This should close if Mathlib has a StarConvex -> path/preconnected theorem.
  -- Otherwise the error tells us the exact theorem name gap.
  exact ?starconvex_to_preconnected

end

end RHFormalization
