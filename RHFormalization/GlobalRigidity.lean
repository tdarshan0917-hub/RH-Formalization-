import RHFormalization.InterfaceAlgebra

/-!
# RHFormalization.GlobalRigidity

Iteration 4: refine the Appendix-F global rigidity layer.

The manuscript's Appendix F step is:

1. Appendix E supplies the local identity on the overlap half-plane:
      `FH = Htot - Zpole`.
2. The meromorphic identity theorem globalizes this identity to all of `Ω`.
3. Since `FH` and `Htot` are holomorphic on `Ω`, the zero-side package cannot
   have an uncancelled pole inside `Ω`.

This file does not yet discharge the analytic meromorphic identity theorem in
Mathlib. Instead, it represents that theorem as a precise API and derives the
previous monolithic no-pole rigidity API from smaller, auditable components.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Global identity produced by Appendix F
-/

/--
Global identity on `Ω`:

`FH = Htot - Zpole`.

This is the result of applying the meromorphic identity theorem to the local
identity from `InterfaceAlgebra.lean`.
-/
structure GlobalIdentityAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_global_identity :
    Set.EqOn D.FH (fun s => Htot D H s - H.Zpole s) Ω

/--
The meromorphic identity theorem as a precise formal interface.

It consumes the already-proved local split on the overlap half-plane and returns
the global identity on `Ω`.

Later, this structure should be replaced by a theorem using Mathlib's
meromorphic identity theorem once all hypotheses are represented natively.
-/
structure MeromorphicIdentityTheoremAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_globalize :
    Set.EqOn D.FH (fun s => Htot D H s - H.Zpole s) (InterfaceOverlap E) →
    Set.EqOn D.FH (fun s => Htot D H s - H.Zpole s) Ω

/--
Build the global identity from the local Appendix-E identity and the
meromorphic identity theorem API.
-/
def buildGlobalIdentity
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (M : MeromorphicIdentityTheoremAPI D H E) :
    GlobalIdentityAPI D H E :=
  { h_global_identity :=
      M.h_globalize (local_split_eqOn D H E) }

/-!
## 2. Holomorphic shield
-/

/--
Holomorphic shield used in Appendix F.

`FH` is holomorphic on `Ω` by Appendix D.
`Htot = RH + Harch` is holomorphic on `Ω` from Appendix D and Appendix H
plus holomorphic closure under addition.
-/
structure HolomorphicShieldAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  h_FH_holo :
    HolomorphicOnC D.FH Ω
  h_Htot_holo :
    HolomorphicOnC (Htot D H) Ω

/--
Build the shield when the holomorphy of `Htot` has already been supplied.

The holomorphy of `Htot` is deliberately explicit: this prevents Lean from
silently treating holomorphic closure under addition as already formalized.
-/
def buildHolomorphicShield
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (h_Htot : HolomorphicOnC (Htot D H) Ω) :
    HolomorphicShieldAPI D H :=
  { h_FH_holo := D.hFH_holo
    h_Htot_holo := h_Htot }

/--
Small API for the holomorphic closure step:
if `RH` and `Harch` are holomorphic, then `Htot = RH + Harch` is holomorphic.
-/
structure HtotHolomorphicAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  h_Htot_holo :
    HolomorphicOnC (Htot D H) Ω

/-- Build the holomorphic shield from the explicit `Htot` holomorphy API. -/
def buildHolomorphicShieldFromAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (A : HtotHolomorphicAPI D H) :
    HolomorphicShieldAPI D H :=
  buildHolomorphicShield D H A.h_Htot_holo

/-!
## 3. No-cancellation / removable-singularity obstruction
-/

/--
No-pole consequence of the global identity and holomorphic shield.

Mathematically: if `FH = Htot - Zpole` globally on `Ω`, and both `FH` and
`Htot` are holomorphic at a point of `Ω`, then `Zpole` cannot have a genuine
uncancelled pole there.

This is the local pole-removal / non-cancellation lemma that will later be
discharged using meromorphic normal forms.
-/
structure NoPoleFromGlobalIdentityAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_no_genuine_pole :
    GlobalIdentityAPI D H E →
    HolomorphicShieldAPI D H →
    ∀ W : ZeroWitness, ¬ HasGenuinePole H.Zpole W.s0

/--
The assembled Appendix-F no-pole shield.

This is the same object previously used in `RigidityBridge`, but now it is
derived from smaller pieces rather than being a single opaque API.
-/
structure RigidityNoPoleAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  globalIdentity :
    GlobalIdentityAPI D H E
  holomorphicShield :
    HolomorphicShieldAPI D H
  h_no_genuine_pole :
    ∀ W : ZeroWitness, ¬ HasGenuinePole H.Zpole W.s0

/-- Assemble the no-pole rigidity API from the three Appendix-F components. -/
def buildRigidityNoPole
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (G : GlobalIdentityAPI D H E)
    (S : HolomorphicShieldAPI D H)
    (N : NoPoleFromGlobalIdentityAPI D H E) :
    RigidityNoPoleAPI D H E :=
  { globalIdentity := G
    holomorphicShield := S
    h_no_genuine_pole := N.h_no_genuine_pole G S }

/--
Convenience assembly from the meromorphic identity theorem API,
the holomorphic `Htot` API, and the no-pole obstruction API.
-/
def buildRigidityNoPoleFromGlobalLayer
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (A : HtotHolomorphicAPI D H)
    (N : NoPoleFromGlobalIdentityAPI D H E) :
    RigidityNoPoleAPI D H E :=
  buildRigidityNoPole D H E
    (buildGlobalIdentity D H E M)
    (buildHolomorphicShieldFromAPI D H A)
    N

end

end RHFormalization
