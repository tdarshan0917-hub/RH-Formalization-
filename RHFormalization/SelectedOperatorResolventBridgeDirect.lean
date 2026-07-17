import RHFormalization.CurrentFrontierSelectedD

namespace RHFormalization
noncomputable section

/--
Direct selected D-side operator bridge.

This bypasses the stale selected-Y wrapper that asks for the impossible
`∀ α : DFiniteStage` residual bound.  The final E/F spine only needs the
`OperatorResolventBridge`, and that can be built directly from the actual
D-export ingredients: B, F, R, and overlap.
-/
def selectedOperatorResolventBridgeDirect
    (B : DBcanLimitData selectedFiniteOperatorLayer.toStagePackage)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (O : DOverlapIdentityAPI selectedFiniteOperatorLayer.toStagePackage B F R) :
    OperatorResolventBridge :=
  buildOperatorResolventBridgeFromDExport
    { P := selectedFiniteOperatorLayer.toStagePackage
      B := B
      F := F
      R := R
      canRem :=
        { h_remainder_holo := R.h_RH_holo
          h_can_rem_convergence := R.h_R_stage_to_RH }
      overlap := O }

#print axioms selectedOperatorResolventBridgeDirect

end
end RHFormalization
