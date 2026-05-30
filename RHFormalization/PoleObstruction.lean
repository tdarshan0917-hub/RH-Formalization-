import RHFormalization.GlobalRigidity

/-!
# RHFormalization.PoleObstruction

Iteration 5: local pole-obstruction layer.

The manuscript's Appendix-F contradiction has a local analytic core:

If

  `FH = Htot - Zpole`

near a point `s0 ∈ Ω`, and `FH` and `Htot` are holomorphic at `s0`, then
`Zpole` cannot have a genuine uncancelled pole at `s0`.

This file makes that local core explicit. The local equality and holomorphy-at notions are now routed through `AnalyticWrappers.lean`; the meromorphic normal-form theorem remains an explicit API. The layer is split into:

* local equality at a witness point;
* holomorphic-on-to-holomorphic-at transfer;
* genuine pole normal-form witness;
* local removable-singularity / pole-obstruction lemma.

This is the next refinement after `GlobalRigidity.lean`.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Local equality at a witness point
-/

/--
From a global `Set.EqOn` identity on `Ω`, obtain local equality at every witness
point `W.s0 ∈ Ω`.

This is a small topological step: since `W.s0 ∈ Ω` and `Ω` is open, equality
on `Ω` gives equality in a neighbourhood of `W.s0`.
-/
structure LocalEqualityAtWitnessAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_local_eq :
    GlobalIdentityAPI D H E →
    ∀ W : ZeroWitness,
      LocalEqAtC D.FH (fun s => Htot D H s - H.Zpole s) W.s0

/-!
## 2. Holomorphic-at shield
-/

/--
Transfer holomorphy on `Ω` to holomorphy at a witness point.

Later this should be discharged by `HolomorphicOn.holomorphicAt` plus openness
of `Ω`.
-/
structure HolomorphicOnToAtAPI where
  h_to_at :
    ∀ (f : ℂ → ℂ) (z : ℂ),
      z ∈ Ω →
      HolomorphicOnC f Ω →
      HolomorphicAtC f z

/--
Witness-level holomorphic shield.

This is the local version of the global holomorphic shield:
`FH` and `Htot` are holomorphic at every forbidden-pole witness point.
-/
structure HolomorphicAtWitnessShieldAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  h_FH_at :
    ∀ W : ZeroWitness, HolomorphicAtC D.FH W.s0
  h_Htot_at :
    ∀ W : ZeroWitness, HolomorphicAtC (Htot D H) W.s0

/-- Build the witness-level shield from the global shield and the on-to-at transfer. -/
def buildHolomorphicAtWitnessShield
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (T : HolomorphicOnToAtAPI)
    (S : HolomorphicShieldAPI D H) :
    HolomorphicAtWitnessShieldAPI D H :=
  { h_FH_at := fun W =>
      T.h_to_at D.FH W.s0 W.hs0_in_Omega S.h_FH_holo
    h_Htot_at := fun W =>
      T.h_to_at (Htot D H) W.s0 W.hs0_in_Omega S.h_Htot_holo }

/-!
## 3. Genuine pole normal form
-/

/--
A genuine pole normal form at a point.

The nonzero principal coefficient is the formal version of the manuscript's
"uncancelled pole" or "grouped residue non-cancellation" condition.
-/
structure GenuinePoleNormalForm
    (f : ℂ → ℂ)
    (s0 : ℂ) where
  principalCoeff : ℂ
  h_principalCoeff_ne_zero : principalCoeff ≠ 0
  h_principalPart : HasPrincipalPartAtC f s0 principalCoeff

/--
Normal-form ownership for the H-side pole package.

This is a refinement of `PoleWitnessAPI`: it records that the genuine pole is
witnessed by a nonzero principal coefficient.
-/
structure GenuinePoleNormalFormAPI
    (H : ZeroPolePackageAPI) where
  h_normal_form :
    ∀ W : ZeroWitness,
      HasGenuinePole H.Zpole W.s0 →
      GenuinePoleNormalForm H.Zpole W.s0

/-!
## 4. Local pole-obstruction lemma
-/

/--
Local analytic pole obstruction.

Mathematically:

If `FH = Htot - Zpole` locally at `W.s0`, and both `FH` and `Htot`
are holomorphic at `W.s0`, then `Zpole` cannot have a genuine pole at `W.s0`.

This is the removable-singularity / no-cancellation lemma that will later be
discharged using meromorphic normal forms.
-/
structure LocalPoleObstructionAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_no_pole_from_local_identity :
    ∀ W : ZeroWitness,
      LocalEqAtC D.FH (fun s => Htot D H s - H.Zpole s) W.s0 →
      HolomorphicAtC D.FH W.s0 →
      HolomorphicAtC (Htot D H) W.s0 →
      ¬ HasGenuinePole H.Zpole W.s0

/--
Build the old `NoPoleFromGlobalIdentityAPI` from the newly split local
pole-obstruction components.

This is the main Iteration-5 bridge.
-/
def buildNoPoleFromPoleObstruction
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (L : LocalEqualityAtWitnessAPI D H E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI D H E) :
    NoPoleFromGlobalIdentityAPI D H E :=
  { h_no_genuine_pole := fun G S W =>
      O.h_no_pole_from_local_identity W
        (L.h_local_eq G W)
        ((buildHolomorphicAtWitnessShield D H T S).h_FH_at W)
        ((buildHolomorphicAtWitnessShield D H T S).h_Htot_at W) }

/--
Convenience assembly of the full no-pole rigidity layer from:
* global meromorphic identity theorem;
* Htot holomorphy;
* local equality extraction;
* holomorphic-on-to-at transfer;
* local pole obstruction.
-/
def buildRigidityNoPoleFromPoleObstructionLayer
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (A : HtotHolomorphicAPI D H)
    (L : LocalEqualityAtWitnessAPI D H E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI D H E) :
    RigidityNoPoleAPI D H E :=
  buildRigidityNoPoleFromGlobalLayer D H E M A
    (buildNoPoleFromPoleObstruction D H E L T O)

end

end RHFormalization
