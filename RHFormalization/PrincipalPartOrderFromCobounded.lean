import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.LocalOrderObstruction

/-!
# RHFormalization.PrincipalPartOrderFromCobounded

This file narrows `PrincipalPartNegativeOrderAPI`.

Instead of assuming directly that a principal-part normal form has negative
meromorphic order, we derive that conclusion from two smaller local facts:

1. the principal-part normal form is meromorphic at the point;
2. the function tends to infinity/cobounded on the punctured neighbourhood.

Mathlib then supplies the equivalence:

`tendsto_cobounded_iff_meromorphicOrderAt_neg`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
A principal-part normal form gives meromorphicity at the pole point.

This remains a local analytic proof obligation, but it is narrower than the full
negative-order statement.
-/
structure PrincipalPartMeromorphicAtAPI where
  h_meromorphicAt :
    ∀ (f : ℂ → ℂ) (s0 coeff : ℂ),
      PrincipalPartNormalForm f s0 coeff →
        MeromorphicAt f s0

/--
A principal-part normal form with nonzero coefficient tends to infinity on the
punctured neighbourhood of the pole point.

This is the analytic non-removability/coboundedness input.
-/
structure PrincipalPartCoboundedAPI where
  h_cobounded :
    ∀ (f : ℂ → ℂ) (s0 coeff : ℂ),
      PrincipalPartNormalForm f s0 coeff →
        Tendsto f (𝓝[≠] s0) (Bornology.cobounded ℂ)

/--
Build the previous `PrincipalPartNegativeOrderAPI` from meromorphicity plus
coboundedness, using Mathlib's meromorphic-order theorem.
-/
def buildPrincipalPartNegativeOrderAPIFromCobounded
    (M : PrincipalPartMeromorphicAtAPI)
    (C : PrincipalPartCoboundedAPI) :
    PrincipalPartNegativeOrderAPI :=
  { h_negative_order := fun f s0 coeff hpp =>
      (tendsto_cobounded_iff_meromorphicOrderAt_neg
        (M.h_meromorphicAt f s0 coeff hpp)).1
        (C.h_cobounded f s0 coeff hpp) }

/--
Endpoint after replacing `PrincipalPartNegativeOrderAPI` by the two narrower
local principal-part inputs.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_principalPartCobounded
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (M : PrincipalPartMeromorphicAtAPI)
    (C : PrincipalPartCoboundedAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_orderObstruction
    ZF
    Y
    X
    E
    I
    (buildPrincipalPartNegativeOrderAPIFromCobounded M C)

end

end RHFormalization
