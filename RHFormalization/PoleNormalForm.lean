import RHFormalization.HSideResidueArithmetic

/-!
# RHFormalization.PoleNormalForm

Iteration 15: pole-normal-form interface.

Appendix F uses a local analytic fact:

If a meromorphic function has a nonzero principal part at `s0`, then it has a
genuine pole at `s0`. Conversely, the final contradiction uses the fact that a
holomorphic identity cannot hide such a nonzero principal part.

Earlier iterations carried this as the opaque API

  `PrincipalPartImpliesGenuinePoleAPI`.

This file refines that API into a local normal-form layer:

* a local Laurent/principal-part model;
* a normal-form object carrying a nonzero coefficient;
* a builder from `HasPrincipalPartAtC`;
* a bridge back to `PrincipalPartImpliesGenuinePoleAPI`.

The hard analytic theorem is still not fully discharged: we have not yet replaced
`HasPrincipalPartAtC` and `HasGenuinePole` by Mathlib/project-local Laurent series
definitions.  But the interface is now narrow and faithful.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Local Laurent model
-/

/--
Project-local placeholder for the local Laurent model

`f(s) = coeff / (s - s0) + holomorphic`.

Later this should be replaced by a genuine Laurent-series or meromorphic-normal-form
definition.
-/
abbrev LocalLaurentPrincipalModelC
    (f : ℂ → ℂ)
    (s0 coeff : ℂ) : Prop :=
  HasPrincipalPartAtC f s0 coeff

/--
A concrete nonzero principal-part normal form.
-/
structure PrincipalPartNormalForm
    (f : ℂ → ℂ)
    (s0 coeff : ℂ) where
  h_coeff_ne_zero :
    coeff ≠ 0
  h_principalPart :
    HasPrincipalPartAtC f s0 coeff
  h_localModel :
    LocalLaurentPrincipalModelC f s0 coeff

/--
Builder from the project principal-part predicate to an explicit normal form.

This remains a hard local meromorphic-analysis API until `HasPrincipalPartAtC` is
defined through Laurent series.
-/
structure PrincipalPartToNormalFormAPI where
  h_to_normal_form :
    ∀ (f : ℂ → ℂ) (s0 coeff : ℂ),
      coeff ≠ 0 →
      HasPrincipalPartAtC f s0 coeff →
      PrincipalPartNormalForm f s0 coeff

/--
Definition-level bridge from a nonzero local normal form to `HasGenuinePole`.

This remains a hard API only because `HasGenuinePole` is still a project wrapper.
Once `HasGenuinePole` is defined as existence of such a normal form, this bridge
should become definitional.
-/
structure NormalFormImpliesGenuinePoleAPI where
  h_genuine :
    ∀ (f : ℂ → ℂ) (s0 coeff : ℂ),
      PrincipalPartNormalForm f s0 coeff →
      HasGenuinePole f s0

/--
A bundled local pole-normal-form layer.
-/
structure PoleNormalFormLayer where
  principalPartToNormalForm :
    PrincipalPartToNormalFormAPI
  normalFormToGenuinePole :
    NormalFormImpliesGenuinePoleAPI

/--
Recover the old `PrincipalPartImpliesGenuinePoleAPI` from the refined
normal-form layer.
-/
def PoleNormalFormLayer.toPrincipalPartImpliesGenuinePoleAPI
    (L : PoleNormalFormLayer) :
    PrincipalPartImpliesGenuinePoleAPI :=
  { h_genuine := fun f s0 c hc hpp =>
      L.normalFormToGenuinePole.h_genuine f s0 c
        (L.principalPartToNormalForm.h_to_normal_form f s0 c hc hpp) }

/-!
## 2. H-side grouped-pole data using the normal-form layer
-/

/--
H-side grouped-pole data where the old `PrincipalPartImpliesGenuinePoleAPI`
is not supplied directly.  Instead, it is built from `PoleNormalFormLayer`.
-/
structure HSideGroupedPoleNormalFormData
    (H : ZeroPolePackageAPI) where
  M : ZeroMultiplicityData
  groupedClass :
    ∀ W : ZeroWitness, GroupedPoleClass M W
  h_principalPart :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC H.Zpole W.s0
        (groupedResidueCoeff M (groupedClass W))
  poleNormalForm :
    PoleNormalFormLayer

/--
Convert normal-form grouped-pole data into the arithmetic grouped-pole data of
Iteration 14.
-/
def HSideGroupedPoleNormalFormData.toArithmeticData
    {H : ZeroPolePackageAPI}
    (A : HSideGroupedPoleNormalFormData H) :
    HSideGroupedPoleArithmeticData H :=
  { M := A.M
    groupedClass := A.groupedClass
    h_principalPart := A.h_principalPart
    principalPartToPole :=
      A.poleNormalForm.toPrincipalPartImpliesGenuinePoleAPI }

/--
Convert normal-form grouped-pole data directly to the H-side pole witness layer.
-/
def HSideGroupedPoleNormalFormData.toHSidePoleWitnessLayer
    {H : ZeroPolePackageAPI}
    (A : HSideGroupedPoleNormalFormData H) :
    HSidePoleWitnessLayer H :=
  A.toArithmeticData.toHSidePoleWitnessLayer

/-!
## 3. H meromorphic package with normal-form grouped poles
-/

/--
H-side meromorphic package plus grouped-pole data whose pole conversion is supplied
by the local pole-normal-form layer.
-/
structure HMeromorphicWithNormalFormPoles where
  layer : HMeromorphicPackageLayerV2
  normalFormGroupedLayer :
    HSideGroupedPoleNormalFormData
      (buildZeroPolePackageFromHMeromorphicLayer layer)

/-- Extract the finished zero-side package. -/
def HMeromorphicWithNormalFormPoles.toZeroPolePackageAPI
    (X : HMeromorphicWithNormalFormPoles) :
    ZeroPolePackageAPI :=
  buildZeroPolePackageFromHMeromorphicLayer X.layer

/-- Extract the H-side pole witness layer. -/
def HMeromorphicWithNormalFormPoles.toHSidePoleWitnessLayer
    (X : HMeromorphicWithNormalFormPoles) :
    HSidePoleWitnessLayer X.toZeroPolePackageAPI :=
  X.normalFormGroupedLayer.toHSidePoleWitnessLayer

/--
Convert to the Iteration-14 arithmetic H-side package object.
-/
def HMeromorphicWithNormalFormPoles.toArithmeticGroupedPoles
    (X : HMeromorphicWithNormalFormPoles) :
    HMeromorphicWithArithmeticGroupedPoles :=
  { layer := X.layer
    arithmeticGroupedLayer := X.normalFormGroupedLayer.toArithmeticData }

end

end RHFormalization
