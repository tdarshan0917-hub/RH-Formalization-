import Mathlib
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
import RHFormalization.OmegaTopology

/-!
# RHFormalization.DefaultOmegaPreperfect

Discharges `OmegaPreperfectAPI`.

Since `Ω` is open in the perfect space `ℂ`, Mathlib's theorem

`IsOpen.preperfect`

gives `Preperfect Ω`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
The slit plane `Ω` is preperfect.

This follows from Mathlib's theorem that every open subset of a perfect space is
preperfect, together with the already theorem-backed openness of `Ω`.
-/
theorem preperfect_Omega_native :
    Preperfect Ω :=
  isOpen_Omega_native.preperfect

/--
Default theorem-backed implementation of `OmegaPreperfectAPI`.
-/
def defaultOmegaPreperfectAPI : OmegaPreperfectAPI :=
  { h_preperfect_Omega := preperfect_Omega_native }

/--
Endpoint after discharging `OmegaPreperfectAPI`.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_codiscreteIdentity`,
this theorem no longer requires:

`OPP : OmegaPreperfectAPI`.

It only requires the Ω-codiscrete meromorphic identity package.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_codiscreteIdentity_preperfect
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (OCI : OmegaCodiscreteMeromorphicIdentityAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_codiscreteIdentity
    ZF
    Y
    X
    E
    OCI
    defaultOmegaPreperfectAPI

end

end RHFormalization
