import RHFormalization.SelectedDirectFinalAssemblyAttempt
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/--
Selected-direct final assembly.

This is the active endgame wrapper:
  selected D bridge + API-level H side + real-zero-free
  ⟹ RiemannHypothesis.

No FinalRHAssembly.
No hpoint route.
No clean-Laplace comparison.
-/
theorem selected_direct_final_RH
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
    (P : PoleWitnessAPI H)
    (Rig :
      RigidityNoPoleAPI
        (selectedOperatorResolventBridgeDirect_from_final_D_inputs
          C L F R hR_alpha hF_alpha hσ)
        H E) :
    RiemannHypothesis :=
  RH_from_selected_direct_D_final_inputs
    h_real_zero_free
    C L F R hR_alpha hF_alpha hσ
    H E P Rig

#print axioms selected_direct_final_RH

end
end RHFormalization
