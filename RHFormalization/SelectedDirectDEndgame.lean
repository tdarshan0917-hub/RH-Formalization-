import RHFormalization.SelectedDirectDRouteFinalInputs
import RHFormalization.FinalSpineFromRealZeroFree

namespace RHFormalization
noncomputable section
open Complex

/--
Selected direct-D endgame.

This proves the selected direct D bridge actually feeds the final RH spine.
No selectedY wrapper. No all-stage h_R_stage_bound.
-/
theorem RH_from_selected_direct_D_final_inputs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData selectedFiniteOperatorLayer C)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (hR_alpha : R.alpha = F.alpha)
    (hF_alpha : F.alpha = L.alpha)
    (hσ : 0 ≤ selectedFiniteOperatorLayer.toStagePackage.sigma0)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI
      (selectedOperatorResolventBridgeDirect_from_final_D_inputs
        C L F R hR_alpha hF_alpha hσ)
      H)
    (P : PoleWitnessAPI H)
    (Rig : RigidityNoPoleAPI
      (selectedOperatorResolventBridgeDirect_from_final_D_inputs
        C L F R hR_alpha hF_alpha hσ)
      H E) :
    RiemannHypothesis :=
  RH_follows_from_realZeroFree_and_APIs
    h_real_zero_free
    (selectedOperatorResolventBridgeDirect_from_final_D_inputs
      C L F R hR_alpha hF_alpha hσ)
    H E P Rig

#print axioms RH_from_selected_direct_D_final_inputs

end
end RHFormalization
