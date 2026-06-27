import RHFormalization.SelectedDirectFinalAssembly
import RHFormalization.FSideWrapperBuilders
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/--
Selected-direct final assembly with the Rigidity API built from the existing
F-side wrapper layer.

This removes `Rig : RigidityNoPoleAPI ...` as a raw input.
-/
theorem selected_direct_final_RH_from_wrapper_layer
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer C)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (hR_alpha : R.alpha = F.alpha)
    (hF_alpha : F.alpha = L.alpha)
    (hσ : 0 ≤ selectedFiniteOperatorLayer.toStagePackage.sigma0)
    (H : ZeroPolePackageAPI)
    (E :
      InterfaceBridgeAPI
        (selectedOperatorResolventBridgeDirect_from_final_D_inputs
          C L F R hR_alpha hF_alpha hσ)
        H)
    (PW : PoleWitnessAPI H)
    (O : OpenOmegaAPI)
    (M :
      MeromorphicIdentityTheoremAPI
        (selectedOperatorResolventBridgeDirect_from_final_D_inputs
          C L F R hR_alpha hF_alpha hσ)
        H E)
    (LP :
      LocalPoleObstructionAPI
        (selectedOperatorResolventBridgeDirect_from_final_D_inputs
          C L F R hR_alpha hF_alpha hσ)
        H E) :
    RiemannHypothesis :=
  selected_direct_final_RH
    C L F R hR_alpha hF_alpha hσ
    H E PW
    (buildRigidityNoPoleFromWrapperLayer
      O
      (selectedOperatorResolventBridgeDirect_from_final_D_inputs
        C L F R hR_alpha hF_alpha hσ)
      H E M LP)

#print axioms selected_direct_final_RH_from_wrapper_layer

end
end RHFormalization
