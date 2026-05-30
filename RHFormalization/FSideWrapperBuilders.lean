import RHFormalization.PoleObstruction

/-!
# RHFormalization.FSideWrapperBuilders

Iteration 11: discharge easy F-side wrapper APIs.

Iteration 10 introduced Mathlib-facing wrappers:

* `HolomorphicOnC := AnalyticOn ℂ`
* `HolomorphicAtC := AnalyticAt ℂ`
* `LocalEqAtC := EventuallyEq at 𝓝 z`

This file uses those wrappers to build three APIs that were previously passed
as assumptions:

1. `HolomorphicOnToAtAPI`
2. `LocalEqualityAtWitnessAPI`
3. `HtotHolomorphicAPI`

The only remaining input for these builders is `OpenOmegaAPI`,
which supplies openness of the manuscript slit plane `Ω`.

The genuinely hard F-side item remains `LocalPoleObstructionAPI`, i.e. the
local meromorphic normal-form/removable-singularity theorem.
-/


namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-!
## 1. Holomorphic algebra for `Htot`
-/

/--
Addition closure for the project holomorphy wrapper.

Since `HolomorphicOnC` is now an abbreviation for `AnalyticOn ℂ`, this is the
Mathlib-facing analytic addition theorem in project notation.
-/
theorem holomorphicOnC_add
    {f g : ℂ → ℂ}
    {U : Set ℂ}
    (hf : HolomorphicOnC f U)
    (hg : HolomorphicOnC g U) :
    HolomorphicOnC (fun s => f s + g s) U := by
  exact hf.add hg

/--
Build `HtotHolomorphicAPI` from the D-side holomorphic remainder and H-side
holomorphic archimedean term.

Mathematically:
`Htot = RH + Harch`, and holomorphic functions are closed under addition.
-/
def buildHtotHolomorphicAPIFromSummands
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) :
    HtotHolomorphicAPI D H :=
  { h_Htot_holo := by
      simpa [Htot] using
        (holomorphicOnC_add D.hRH_holo H.hHarch_holo) }

/-!
## 2. Holomorphic-on to holomorphic-at transfer
-/

/--
Build the old `HolomorphicOnToAtAPI` from the Mathlib-facing wrapper lemma.

This removes one previous F-side assumption.
-/
def buildHolomorphicOnToAtAPIFromOmega
    (O : OpenOmegaAPI) :
    HolomorphicOnToAtAPI :=
  { h_to_at := fun f z hz hf =>
      HolomorphicOnC.holomorphicAt O hf hz }

/-!
## 3. Local equality at witness points
-/

/--
Build local equality at every zero witness from the global identity on `Ω`.

This removes another previous F-side assumption.
-/
def buildLocalEqualityAtWitnessAPIFromOmega
    (O : OpenOmegaAPI)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    LocalEqualityAtWitnessAPI D H E :=
  { h_local_eq := fun G W =>
      localEqAtC_of_eqOn_Omega
        O
        W.hs0_in_Omega
        G.h_global_identity }

/-!
## 4. Assembled F-side wrapper layer
-/

/--
Build the full no-pole rigidity package from:
* meromorphic identity theorem API;
* openness of Ω;
* local pole obstruction.

This removes the need to pass `HtotHolomorphicAPI`, `LocalEqualityAtWitnessAPI`,
and `HolomorphicOnToAtAPI` as separate assumptions.
-/
def buildRigidityNoPoleFromWrapperLayer
    (O : OpenOmegaAPI)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (P : LocalPoleObstructionAPI D H E) :
    RigidityNoPoleAPI D H E :=
  buildRigidityNoPoleFromPoleObstructionLayer
    D H E
    M
    (buildHtotHolomorphicAPIFromSummands D H)
    (buildLocalEqualityAtWitnessAPIFromOmega O D H E)
    (buildHolomorphicOnToAtAPIFromOmega O)
    P

end

end RHFormalization
