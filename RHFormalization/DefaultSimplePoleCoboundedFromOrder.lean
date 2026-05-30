import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.DefaultCoboundedAddFiniteLimit

/-!
# RHFormalization.DefaultSimplePoleCoboundedFromOrder

Narrows `SimplePoleCoboundedAPI`.

Instead of assuming directly that

`coeff / (w - s0)`

is cobounded on the punctured neighbourhood, we derive that from the narrower
meromorphic-order statement

`meromorphicOrderAt (fun w => coeff / (w - s0)) s0 < 0`.

Mathlib then supplies:

`tendsto_cobounded_of_meromorphicOrderAt_neg`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Bornology

/--
Narrow simple-pole order input.

This is the exact remaining local analytic fact: a nonzero simple pole has
negative meromorphic order at the pole point.
-/
structure SimplePoleNegativeOrderAPI where
  h_simple_pole_negative_order :
    ∀ (s0 coeff : ℂ),
      coeff ≠ 0 →
        meromorphicOrderAt
          (fun w : ℂ => coeff / (w - s0))
          s0 < 0

/--
Build `SimplePoleCoboundedAPI` from the simple-pole negative-order input.
-/
def buildSimplePoleCoboundedAPIFromNegativeOrder
    (O : SimplePoleNegativeOrderAPI) :
    SimplePoleCoboundedAPI :=
  { h_simple_pole_cobounded := fun s0 coeff hcoeff =>
      tendsto_cobounded_of_meromorphicOrderAt_neg
        (O.h_simple_pole_negative_order s0 coeff hcoeff) }

/--
Endpoint after replacing `SimplePoleCoboundedAPI` by the narrower
`SimplePoleNegativeOrderAPI`.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleOnly`,
this theorem no longer requires:

`SP : SimplePoleCoboundedAPI`.

It only requires the local simple-pole order fact.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleOrder
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (O : SimplePoleNegativeOrderAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleOnly
    ZF
    Y
    X
    E
    I
    (buildSimplePoleCoboundedAPIFromNegativeOrder O)

end

end RHFormalization
