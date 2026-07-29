import RHFormalization.OmegaNormalFormPropagationEndpoint
import RHFormalization.OmegaNormalFormLocalPropagationEndpoint
import RHFormalization.OmegaMeromorphicLocalPropagationEndpoint
import RHFormalization.OmegaMeromorphicZeroPropagationEndpoint
import RHFormalization.OmegaMeromorphicZeroPropagationClopen
import RHFormalization.DefaultZetaZeroFacts
import RHFormalization.EtaPositivity
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.InterfaceFromCommonCshared
import RHFormalization.HMeromorphicWithNormalFormChosenCshared

namespace RHFormalization

noncomputable section

def finalONFP : OmegaNormalFormCodiscretePropagationAPI :=
  buildOmegaNormalFormCodiscretePropagationFromLocal
    (buildOmegaNormalFormLocalPropagationFromMeromorphic
      (buildOmegaMeromorphicLocalPropagationFromZero
        defaultOmegaMeromorphicZeroPropagationAPI))

#check finalONFP

theorem FinalOmegaPropagationProbe
    (X : HMeromorphicWithNormalFormPoles)
    (h_common : designedY.B.Cshared = X.layer.overlap.Cshared) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormPropagation
    (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
    designedY
    X
    (buildInterfaceBridgeNonnegativeFromCommonCshared designedY X h_common)
    finalONFP

#print axioms finalONFP
#print axioms FinalOmegaPropagationProbe

end
end RHFormalization
