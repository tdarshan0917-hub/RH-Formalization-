import RHFormalization.OmegaTopology
import RHFormalization.GlobalMeromorphicIdentity
import Mathlib.Analysis.Complex.Basic
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
#check mem_Omega_iff_re_pos_or_im_ne_zero

#check Complex.slitPlane
#print Complex.slitPlane
#check Complex.mem_slitPlane_iff
#check Complex.mem_slitPlane_iff_not_le_zero
#check Complex.compl_Iic_zero

#check IsPreconnected
#check IsPathConnected
#check IsPathConnected.isPreconnected
#check Convex.isPreconnected

end

end RHFormalization
