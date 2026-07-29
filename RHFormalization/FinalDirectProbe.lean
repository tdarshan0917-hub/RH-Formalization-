import RHFormalization.AppendixESharedPackageCompatibility
import RHFormalization.DefaultZetaZeroFacts
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.EtaPositivity

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem final_RH_direct_probe : RiemannHypothesis :=
  finalRHSpine_after_directCsharedEq
    (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
    designedY
    ?X
    ?hC

end
end RHFormalization
