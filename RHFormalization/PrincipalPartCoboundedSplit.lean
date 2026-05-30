import Mathlib
import RHFormalization.PrincipalPartCoboundedModel

/-!
# RHFormalization.PrincipalPartCoboundedSplit

Further narrows `SimplePolePlusHolomorphicCoboundedAPI`.

Instead of assuming coboundedness of

`coeff / (w - s0) + h w`

directly, we reduce it to two smaller local facts:

1. the pure nonzero simple pole is cobounded on the punctured neighbourhood;
2. adding a finite-limit perturbation preserves coboundedness.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
A nonzero simple pole tends to infinity/cobounded on the punctured neighbourhood.
-/
structure SimplePoleCoboundedAPI where
  h_simple_pole_cobounded :
    ∀ (s0 coeff : ℂ),
      coeff ≠ 0 →
        Tendsto
          (fun w : ℂ => coeff / (w - s0))
          (𝓝[≠] s0)
          (Bornology.cobounded ℂ)

/--
Adding a finite-limit perturbation to a cobounded function preserves coboundedness.
-/
structure CoboundedAddFiniteLimitAPI where
  h_add_finite_limit :
    ∀ (f g : ℂ → ℂ) (l : Filter ℂ) (c : ℂ),
      Tendsto f l (Bornology.cobounded ℂ) →
      Tendsto g l (𝓝 c) →
        Tendsto
          (fun w : ℂ => f w + g w)
          l
          (Bornology.cobounded ℂ)

/--
Build the previous `SimplePolePlusHolomorphicCoboundedAPI` from the two narrower
local coboundedness facts.
-/
def buildSimplePolePlusHolomorphicCoboundedAPIFromSplit
    (SP : SimplePoleCoboundedAPI)
    (BA : CoboundedAddFiniteLimitAPI) :
    SimplePolePlusHolomorphicCoboundedAPI :=
  { h_model_cobounded := fun h s0 coeff hcoeff hh =>
      by
        have hpole :
            Tendsto
              (fun w : ℂ => coeff / (w - s0))
              (𝓝[≠] s0)
              (Bornology.cobounded ℂ) :=
          SP.h_simple_pole_cobounded s0 coeff hcoeff

        have hh_nhds :
            Tendsto h (𝓝 s0) (𝓝 (h s0)) :=
          hh.continuousAt.tendsto

        have hh_punct :
            Tendsto h (𝓝[≠] s0) (𝓝 (h s0)) :=
          hh_nhds.mono_left nhdsWithin_le_nhds

        exact
          BA.h_add_finite_limit
            (fun w : ℂ => coeff / (w - s0))
            h
            (𝓝[≠] s0)
            (h s0)
            hpole
            hh_punct }

/--
Endpoint after replacing `SimplePolePlusHolomorphicCoboundedAPI` by the two
narrower coboundedness facts.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_splitCobounded
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (SP : SimplePoleCoboundedAPI)
    (BA : CoboundedAddFiniteLimitAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleCobounded
    ZF
    Y
    X
    E
    I
    (buildSimplePolePlusHolomorphicCoboundedAPIFromSplit SP BA)

end

end RHFormalization
