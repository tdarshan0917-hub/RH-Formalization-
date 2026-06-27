import RHFormalization.ShiftedLaplaceRepDirectFrontier
import RHFormalization.AppendixESharedCanonicalPackage
import RHFormalization.InterfaceBridgeNonnegativeFromPlain
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/--
Direct Appendix-E shared-package evidence for the corrected Rep H-side.

This bypasses `HMeromorphicPackageLayerV2`; the H package is the direct
`ZeroPolePackageAPI` constructed for `ZpoleRepSeries`.
-/
noncomputable def shiftedLaplaceRepSharedCanonicalEvidence
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ))
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z)
    (h_common :
      Y.B.Cshared = shiftedLaplacePrimePackageAt 1) :
    SharedCanonicalPackageEvidence
      Y.toOperatorResolventBridge
      (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
        ZF hbridge hB_regular) :=
  { Bshared := (shiftedLaplacePrimePackageAt 1).Bshared
    sigma := max Y.toOperatorResolventBridge.sigma0 1
    hsigma_ge_D := le_max_left _ _
    hsigma_ge_H := by
      dsimp [shiftedLaplaceRepZeroPolePackageFromBridgeBregular,
        shiftedLaplaceRepZeroPolePackageDirect]
      exact le_max_right _ _
    h_D_matches_shared := by
      intro s hs
      have hsD :
          s ∈ RightHalfPlane Y.toOperatorResolventBridge.sigma0 :=
        RightHalfPlane_subset_of_le
          (le_max_left Y.toOperatorResolventBridge.sigma0 1)
          hs
      have hD := Y.B.h_Bcan_matches_shared s hsD
      simpa [h_common] using hD
    h_H_matches_shared := by
      intro s hs
      rfl }

/-- Direct Appendix-E interface bridge for the corrected Rep H-side. -/
noncomputable def shiftedLaplaceRepInterfaceBridge
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ))
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z)
    (h_common :
      Y.B.Cshared = shiftedLaplacePrimePackageAt 1) :
    InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
        ZF hbridge hB_regular) :=
  buildInterfaceBridgeFromSharedCanonicalPackage
    Y.toOperatorResolventBridge
    (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
      ZF hbridge hB_regular)
    (shiftedLaplaceRepSharedCanonicalEvidence
      ZF Y hbridge hB_regular h_common)

#print axioms shiftedLaplaceRepSharedCanonicalEvidence
#print axioms shiftedLaplaceRepInterfaceBridge

end
end RHFormalization
