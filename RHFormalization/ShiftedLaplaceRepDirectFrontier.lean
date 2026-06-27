import RHFormalization.ShiftedLaplaceRepDirectHSide
import RHFormalization.MainTheorem
import RHFormalization.FSideWrapperBuilders
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/--
Direct corrected-Rep H-side witness layer.

This bypasses `HMeromorphicPackageLayerV2`, hence does not require the stale
generic `ZeroPoleLocalUniformConvergenceAPI` slot.
-/
noncomputable def shiftedLaplaceRepHSidePoleWitnessLayerFromBridgeBregular
    (ZF : ZetaZeroFacts)
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ))
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z) :
    HSidePoleWitnessLayer
      (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
        ZF hbridge hB_regular) :=
  (shiftedLaplaceRepNormalFormFromBridgeBregular
    ZF hbridge hB_regular).toHSidePoleWitnessLayer

/--
Direct corrected-Rep frontier.

Inputs left explicit:
  * Appendix-E interface bridge `E`;
  * Appendix-F meromorphic identity package `M`;
  * local pole obstruction `Pobs`.

The easy F-side wrappers `A`, `L`, and `T` are built here.
-/
theorem RH_from_direct_corrected_rep_Hside
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
    (E :
      InterfaceBridgeAPI
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular))
    (M :
      MeromorphicIdentityTheoremAPI
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        E)
    (Pobs :
      LocalPoleObstructionAPI
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_H_grouped_pole_layer
      ZF
      Y.toOperatorResolventBridge
      (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
        ZF hbridge hB_regular)
      E
      (shiftedLaplaceRepHSidePoleWitnessLayerFromBridgeBregular
        ZF hbridge hB_regular)
      M
      (buildHtotHolomorphicAPIFromSummands
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular))
      (buildLocalEqualityAtWitnessAPIFromOmega
        defaultOpenOmegaAPI
        Y.toOperatorResolventBridge
        (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
          ZF hbridge hB_regular)
        E)
      (buildHolomorphicOnToAtAPIFromOmega defaultOpenOmegaAPI)
      Pobs

#print axioms shiftedLaplaceRepHSidePoleWitnessLayerFromBridgeBregular
#print axioms RH_from_direct_corrected_rep_Hside

end
end RHFormalization
