import RHFormalization.PoleNormalForm

/-!
# RHFormalization.PoleObstructionFromNormalForm

Iteration 16: local pole obstruction from principal-part normal forms.

Appendix F uses the following local contradiction:

* `FH = Htot - Zpole` locally near a witness point `s0`;
* `FH` is holomorphic at `s0`;
* `Htot` is holomorphic at `s0`;
* `Zpole` has a nonzero principal-part normal form at `s0`.

These cannot all hold.

Earlier iterations represented the final local step as:

  `LocalPoleObstructionAPI`.

Iteration 16 narrows that API.  We now build `LocalPoleObstructionAPI` from:

* `GenuinePoleNormalFormAPI`, which turns a genuine pole witness into a principal-part record;
* `PoleNormalFormLayer`, which upgrades the principal-part record to a local Laurent normal form;
* `LocalNormalFormObstructionAPI`, the exact local theorem that holomorphic balance is
  incompatible with a nonzero principal part.

The hard theorem is now only `LocalNormalFormObstructionAPI`; the rest of the
bookkeeping is explicit.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Local normal-form obstruction
-/

/--
The local analytic contradiction in Appendix F.

Given local equality
`FH = Htot - Zpole`,
holomorphy of `FH` and `Htot` at the witness point, and a nonzero principal-part
normal form for `Zpole`, contradiction follows.

This is the precise theorem that should later be discharged by a Laurent-series or
meromorphic-normal-form argument.
-/
structure LocalNormalFormObstructionAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) where
  h_no_normal_form :
    ∀ W : ZeroWitness,
    ∀ coeff : ℂ,
      LocalEqAtC D.FH (fun s => Htot D H s - H.Zpole s) W.s0 →
      HolomorphicAtC D.FH W.s0 →
      HolomorphicAtC (Htot D H) W.s0 →
      PrincipalPartNormalForm H.Zpole W.s0 coeff →
      False

/-!
## 2. From genuine-pole normal forms to local obstruction
-/

/--
Convert a `GenuinePoleNormalForm` into the stronger `PrincipalPartNormalForm`,
using the pole-normal-form layer.

This is a pure wrapper/normalization step.
-/
def principalPartNormalFormOfGenuine
    (L : PoleNormalFormLayer)
    {f : ℂ → ℂ}
    {s0 : ℂ}
    (G : GenuinePoleNormalForm f s0) :
    PrincipalPartNormalForm f s0 G.principalCoeff :=
  L.principalPartToNormalForm.h_to_normal_form
    f
    s0
    G.principalCoeff
    G.h_principalCoeff_ne_zero
    G.h_principalPart

/--
Build the previous `LocalPoleObstructionAPI` from the narrower local normal-form
obstruction theorem.

This is the main Iteration-16 construction.
-/
def buildLocalPoleObstructionFromNormalForm
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (N : GenuinePoleNormalFormAPI H)
    (L : PoleNormalFormLayer)
    (O : LocalNormalFormObstructionAPI D H E) :
    LocalPoleObstructionAPI D H E :=
  { h_no_pole_from_local_identity := fun W h_local h_FH_at h_Htot_at h_pole =>
      let G : GenuinePoleNormalForm H.Zpole W.s0 :=
        N.h_normal_form W h_pole
      let PN : PrincipalPartNormalForm H.Zpole W.s0 G.principalCoeff :=
        principalPartNormalFormOfGenuine L G
      O.h_no_normal_form W G.principalCoeff h_local h_FH_at h_Htot_at PN }

/-!
## 3. Extraction from H-side normal-form packages
-/

/--
The zero-side package associated to an `HMeromorphicWithNormalFormPoles` object,
written in the legacy path used by the Iteration-15 endpoint.
-/
def HMeromorphicWithNormalFormPoles.toLegacyZeroPolePackageAPI
    (X : HMeromorphicWithNormalFormPoles) :
    ZeroPolePackageAPI :=
  X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI

/--
The genuine-pole normal-form API extracted from the H-side normal-form package.
-/
def HMeromorphicWithNormalFormPoles.toLegacyGenuinePoleNormalFormAPI
    (X : HMeromorphicWithNormalFormPoles) :
    GenuinePoleNormalFormAPI X.toLegacyZeroPolePackageAPI :=
  let Y : HMeromorphicWithGroupedPoles :=
    X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles
  (Y.toHSidePoleWitnessLayer).toNormalFormAPI

/--
The local pole-normal-form layer carried by the H-side package.
-/
def HMeromorphicWithNormalFormPoles.toPoleNormalFormLayer
    (X : HMeromorphicWithNormalFormPoles) :
    PoleNormalFormLayer :=
  X.normalFormGroupedLayer.poleNormalForm

/--
Build the local pole obstruction API directly from the H-side normal-form package
and the local normal-form obstruction theorem.
-/
def buildLocalPoleObstructionFromHNormalFormPackage
    (D : OperatorResolventBridge)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI D X.toLegacyZeroPolePackageAPI)
    (O : LocalNormalFormObstructionAPI D X.toLegacyZeroPolePackageAPI E) :
    LocalPoleObstructionAPI D X.toLegacyZeroPolePackageAPI E :=
  buildLocalPoleObstructionFromNormalForm
    D
    X.toLegacyZeroPolePackageAPI
    E
    X.toLegacyGenuinePoleNormalFormAPI
    X.toPoleNormalFormLayer
    O

end

end RHFormalization
