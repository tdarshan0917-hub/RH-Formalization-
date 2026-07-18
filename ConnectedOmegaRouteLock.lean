import RHFormalization.GlobalMeromorphicIdentity
import RHFormalization.OmegaTopology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Log
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.Basic

namespace RHFormalization

noncomputable section

open Complex Set

#check ConnectedOmegaAPI
#print ConnectedOmegaAPI

#check Ω
#check Omega
#check NonpositiveRealAxis
#check mem_Omega_iff

#check IsPreconnected
#check IsPathConnected
#check IsPathConnected.isPreconnected
#check Convex.isPreconnected

-- Candidate names. Unknown identifiers are verdicts, not regressions.
#check Complex.slitPlane
#check Complex.isOpen_slitPlane
#check Complex.isPreconnected_slitPlane
#check Complex.isPathConnected_slitPlane
#check isOpen_slitPlane
#check isPreconnected_slitPlane
#check isPathConnected_slitPlane

end

end RHFormalization
