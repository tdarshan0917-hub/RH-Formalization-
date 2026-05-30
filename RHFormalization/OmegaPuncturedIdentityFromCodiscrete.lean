import RHFormalization.OmegaPuncturedIdentityEndpoint
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order

/-!
# RHFormalization.OmegaPuncturedIdentityFromCodiscrete

Narrows `OmegaPuncturedMeromorphicIdentityAPI`.

Mathlib's meromorphic identity infrastructure is naturally codiscrete/punctured,
not pointwise-on-all-poles.  This file replaces the Ω-specific punctured identity
input by:

* a codiscrete meromorphic identity input on Ω;
* a preperfectness input for Ω.

Mathlib then supplies the conversion from codiscrete equality to punctured-neighborhood
equality.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Ω is preperfect.  This is the topological condition needed by Mathlib's
codiscrete-to-punctured meromorphic equality theorem.
-/
structure OmegaPreperfectAPI where
  h_preperfect_Omega :
    Preperfect Ω

/--
Ω-specific codiscrete meromorphic identity principle.

This is weaker and more Mathlib-native than directly asking for punctured equality.
It says that meromorphic functions on Ω agreeing on the overlap agree on a
codiscrete subset of Ω.
-/
structure OmegaCodiscreteMeromorphicIdentityAPI where
  h_codiscrete_identity :
    ∀ (f g : ℂ → ℂ) (V : Set ℂ),
      IsOpen V →
      V.Nonempty →
      V ⊆ Ω →
      MeromorphicOnC f Ω →
      MeromorphicOnC g Ω →
      Set.EqOn f g V →
      f =ᶠ[Filter.codiscreteWithin Ω] g

/--
Build the Ω-specific punctured identity package from a codiscrete identity package
and preperfectness of Ω.
-/
def buildOmegaPuncturedIdentityFromCodiscrete
    (OCI : OmegaCodiscreteMeromorphicIdentityAPI)
    (OPP : OmegaPreperfectAPI) :
    OmegaPuncturedMeromorphicIdentityAPI :=
  { h_punctured_identity := fun f g V z hVopen hVnonempty hVsubset hz hf hg hEq =>
      MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (hf z hz)
        (hg z hz)
        hz
        OPP.h_preperfect_Omega
        (OCI.h_codiscrete_identity f g V hVopen hVnonempty hVsubset hf hg hEq) }

/--
Endpoint after replacing `OmegaPuncturedMeromorphicIdentityAPI` by codiscrete
identity plus preperfectness of Ω.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_codiscreteIdentity
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (OCI : OmegaCodiscreteMeromorphicIdentityAPI)
    (OPP : OmegaPreperfectAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_omegaPuncturedIdentity
    ZF
    Y
    X
    E
    (buildOmegaPuncturedIdentityFromCodiscrete OCI OPP)

end

end RHFormalization
