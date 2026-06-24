import RHFormalization.ResolventOperatorLayer
import RHFormalization.DOperatorExport

/-!
# ResolventOperatorBridgeDirect

THE LIVE ROUTE: build the D-export operator bridge DIRECTLY over the REAL
`resolventOperatorLayer` (F = spectralResolventPartial, real Dirichlet eigenvalues),
bypassing the degenerate selected/spike container entirely.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- Direct operator-resolvent bridge over the REAL resolvent operator layer. -/
def resolventOperatorBridgeDirect
    (B : DBcanLimitData resolventOperatorLayer.toStagePackage)
    (F : DFHLimitData resolventOperatorLayer.toStagePackage)
    (R : DMasterResidualData resolventOperatorLayer.toStagePackage)
    (O : DOverlapIdentityAPI resolventOperatorLayer.toStagePackage B F R) :
    OperatorResolventBridge :=
  buildOperatorResolventBridgeFromDExport
    { P := resolventOperatorLayer.toStagePackage
      B := B
      F := F
      R := R
      canRem :=
        { h_remainder_holo := R.h_RH_holo
          h_can_rem_convergence := R.h_R_stage_to_RH }
      overlap := O }

#print axioms resolventOperatorBridgeDirect

end
end RHFormalization
