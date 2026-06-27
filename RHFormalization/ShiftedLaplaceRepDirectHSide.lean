import RHFormalization.ShiftedLaplaceRepRawRegular
import RHFormalization.ShiftedLaplaceRepDirectPackage
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceBppFromBridge
import RHFormalization.ShiftedLaplaceRepWitnessFromBridge
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/-- Corrected Rep `hBpp` at `sigma0 = 1`, from the shifted Laplace bridge. -/
theorem shiftedLaplaceRep_hBpp_from_bridge_one
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ)) :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)) := by
  exact shiftedLaplace_hBpp_singleton_from_bridge (1 : ℝ) hbridge

/-- Corrected Rep `h_regular` at `sigma0 = 1`, from Bshared regularity. -/
theorem shiftedLaplaceRep_hregular_from_Bregular_one
    (ZF : ZetaZeroFacts)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC (repRaw 1) z :=
  repRaw_one_h_regular_from_Bregular ZF hB_regular

/-- Direct corrected Rep zero-pole package from bridge + Bregular. -/
noncomputable def shiftedLaplaceRepZeroPolePackageFromBridgeBregular
    (ZF : ZetaZeroFacts)
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ))
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z) :
    ZeroPolePackageAPI :=
  shiftedLaplaceRepZeroPolePackageDirect
    ZF
    (shiftedLaplaceRep_hBpp_from_bridge_one hbridge)
    (shiftedLaplaceRep_hregular_from_Bregular_one ZF hB_regular)

/-- Direct corrected Rep normal-form layer from bridge + Bregular. -/
noncomputable def shiftedLaplaceRepNormalFormFromBridgeBregular
    (ZF : ZetaZeroFacts)
    (hbridge : ShiftedLaplaceBridgeData (1 : ℝ))
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z) :
    HSideGroupedPoleNormalFormData
      (shiftedLaplaceRepZeroPolePackageFromBridgeBregular
        ZF hbridge hB_regular) :=
  shiftedLaplaceRepNormalFormGroupedLayerDirect
    ZF
    (shiftedLaplaceRep_hBpp_from_bridge_one hbridge)
    (shiftedLaplaceRep_hregular_from_Bregular_one ZF hB_regular)

#print axioms shiftedLaplaceRep_hBpp_from_bridge_one
#print axioms shiftedLaplaceRep_hregular_from_Bregular_one
#print axioms shiftedLaplaceRepZeroPolePackageFromBridgeBregular
#print axioms shiftedLaplaceRepNormalFormFromBridgeBregular

end
end RHFormalization
