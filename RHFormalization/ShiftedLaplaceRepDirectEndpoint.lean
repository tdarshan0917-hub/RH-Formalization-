import RHFormalization.ShiftedLaplaceRepDirectAppendixE
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/--
Direct corrected-Rep endpoint.

This composes:
  * the direct corrected Rep H-side package;
  * the direct Appendix-E shared canonical package bridge;
  * the direct frontier theorem using `ZeroPolePackageAPI`.

No `HMeromorphicPackageLayerV2`.
No generic representative `ZeroPoleLocalUniformConvergenceAPI`.
-/
theorem RH_from_direct_corrected_rep_shared
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
      Y.B.Cshared = shiftedLaplacePrimePackageAt 1)
    (M :
      MeromorphicIdentityTheoremAPI
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        (shiftedLaplaceRepInterfaceBridge
          ZF Y hbridge hB_regular h_common))
    (Pobs :
      LocalPoleObstructionAPI
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        (shiftedLaplaceRepInterfaceBridge
          ZF Y hbridge hB_regular h_common)) :
    RiemannHypothesis :=
  RH_from_direct_corrected_rep_Hside
    ZF
    Y
    hbridge
    hB_regular
    (shiftedLaplaceRepInterfaceBridge
      ZF Y hbridge hB_regular h_common)
    M
    Pobs

#print axioms RH_from_direct_corrected_rep_shared

end
end RHFormalization
