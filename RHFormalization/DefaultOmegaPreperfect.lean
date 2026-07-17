import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
import RHFormalization.OmegaTopology
import Mathlib.Topology.Perfect

namespace RHFormalization
noncomputable section

theorem preperfect_Omega_native : Preperfect Ω :=
  isOpen_Omega_native.preperfect

def defaultOmegaPreperfectAPI : OmegaPreperfectAPI :=
  { h_preperfect_Omega := preperfect_Omega_native }

#print axioms defaultOmegaPreperfectAPI

end
end RHFormalization
