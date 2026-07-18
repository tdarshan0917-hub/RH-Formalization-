import RHFormalization.GlobalMeromorphicIdentity
import RHFormalization.OmegaTopology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Log
import Mathlib.Topology.PathConnected
import Mathlib.Topology.Connected.PathConnected

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
#check PathConnectedSpace

#check Convex.isPreconnected
#check IsPathConnected.isPreconnected
#check pathConnectedSpace_iff

-- Candidate Mathlib names; unknown identifiers are useful verdicts.
#check Complex.slitPlane
#check Complex.isOpen_slitPlane
#check Complex.isPreconnected_slitPlane
#check Complex.isPathConnected_slitPlane
#check isOpen_slitPlane
#check isPreconnected_slitPlane
#check isPathConnected_slitPlane

end

end RHFormalization
