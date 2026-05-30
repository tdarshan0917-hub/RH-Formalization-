import RHFormalization.HalfPlaneGeometry

/-!
# RHFormalization.InterfaceNonnegative

Iteration 19: nonnegative interface threshold layer.

Appendix E works on a nonempty right half-plane

  Uσ = {s : ℂ | σ < Re s} ⊂ Ω,

with σ chosen beyond the relevant operator/zero-side half-plane thresholds and with
σ ≥ 0.  Iteration 18 still passed this as a loose endpoint parameter:

  `hσ : 0 ≤ E.sigma`.

This file packages that condition into the interface object itself.  The preferred
endpoint now consumes an interface with a nonnegative threshold, rather than a raw
interface plus a separate proof.
-/


namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-!
## 1. Nonnegative interface bridge
-/

/--
Appendix-E interface bridge with the additional condition that its overlap threshold
is nonnegative.

This is the formal version of choosing `σ > max(0, σop, σH)` in the manuscript.
-/
structure InterfaceBridgeNonnegativeAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  bridge : InterfaceBridgeAPI D H
  h_sigma_nonneg :
    0 ≤ bridge.sigma

/-- Coerce a nonnegative interface bridge to the underlying raw interface bridge. -/
def InterfaceBridgeNonnegativeAPI.toInterfaceBridge
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeNonnegativeAPI D H) :
    InterfaceBridgeAPI D H :=
  E.bridge

/--
Extract the `InterfaceSigmaNonnegativeAPI` used by the global identity geometry
layer.
-/
def InterfaceBridgeNonnegativeAPI.toInterfaceSigmaNonnegativeAPI
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeNonnegativeAPI D H) :
    InterfaceSigmaNonnegativeAPI E.bridge :=
  { h_sigma_nonneg := E.h_sigma_nonneg }

/--
Build the overlap geometry directly from a nonnegative interface bridge.
-/
def InterfaceBridgeNonnegativeAPI.toOverlapGeometry
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeNonnegativeAPI D H) :
    OverlapGeometryAPI D H E.bridge :=
  defaultOverlapGeometryAPI D H E.bridge E.h_sigma_nonneg

/-!
## 2. Threshold-choice builder
-/

/--
A threshold-choice package for Appendix E.

This records the manuscript convention that the actual overlap threshold is chosen
large enough to dominate both D- and H-side half-plane thresholds and nonnegative
enough to place the half-plane inside `Ω`.
-/
structure InterfaceThresholdChoiceAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  sigma : ℝ
  h_sigma_nonneg :
    0 ≤ sigma
  h_sigma_ge_D :
    D.sigma0 ≤ sigma
  h_sigma_ge_H :
    H.sigma0 ≤ sigma

/--
Build a nonnegative interface bridge from:
* a threshold choice;
* a raw package-identity proof on that threshold.
-/
def buildInterfaceBridgeNonnegativeAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (T : InterfaceThresholdChoiceAPI D H)
    (h_interface :
      ∀ s : ℂ, s ∈ RightHalfPlane T.sigma →
        D.B s = H.Bzero s) :
    InterfaceBridgeNonnegativeAPI D H :=
  { bridge :=
      { sigma := T.sigma
        hsigma_ge_D := T.h_sigma_ge_D
        hsigma_ge_H := T.h_sigma_ge_H
        h_interface := h_interface }
    h_sigma_nonneg := T.h_sigma_nonneg }

/-!
## 3. Preferred notation helpers
-/

/-- The overlap set attached to a nonnegative interface bridge. -/
def InterfaceBridgeNonnegativeAPI.overlap
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeNonnegativeAPI D H) : Set ℂ :=
  InterfaceOverlap E.bridge

/-- Local split identity for a nonnegative interface bridge. -/
theorem InterfaceBridgeNonnegativeAPI.local_split_eqOn
    {D : OperatorResolventBridge}
    {H : ZeroPolePackageAPI}
    (E : InterfaceBridgeNonnegativeAPI D H) :
    Set.EqOn D.FH
      (fun s => Htot D H s - H.Zpole s)
      E.overlap := by
  exact RHFormalization.local_split_eqOn D H E.bridge

end

end RHFormalization
