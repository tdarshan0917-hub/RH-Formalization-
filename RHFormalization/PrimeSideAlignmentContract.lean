import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.DOperatorExport

/-!
# RHFormalization.PrimeSideAlignmentContract

Model-alignment firewall for the explicit-formula branch.

EF10--EF12 showed that the current concrete B-side is still the
displacement heat package, while pole cancellation requires an `s`-dependent
prime-side transform.  This file stops the loop by naming the correct next
object abstractly.

The intended next target is not:

  displacementCanonicalKernel (heatKernelG 1)

but a transformed prime-side function `Btr : ℂ → ℂ`, eventually to be
identified with `OperatorResolventBridge.B` or with a newly defined
Stieltjes/Laplace/resolvent prime package.
-/

namespace RHFormalization

noncomputable section

open Complex Set

/--
Prime-side alignment contract.

`Btr` is the corrected transformed prime-side object.  It is allowed to be
either:

* `D.B`, the B-field exported by `OperatorResolventBridge`; or
* a newly defined Stieltjes/Laplace/resolvent prime-power transform later
  proved to agree with `D.B` on the overlap half-plane.

The contract records exactly the data needed before returning to local
explicit-formula cancellation.
-/
structure PrimeSideAlignmentContract
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge) where

  /-- The corrected `s`-dependent prime-side transform. -/
  Btr : ℂ → ℂ

  /--
  Alignment with the Appendix-D exported B-function on the overlap half-plane.
  This is the bridge away from the current displacement placeholder.
  -/
  h_Btr_matches_D_on_overlap :
    ∀ s : ℂ, s ∈ RightHalfPlane D.sigma0 →
      Btr s = D.B s

  /--
  Opposite principal parts at zero-witness pole points.

  This is the corrected replacement for the paused
  `h_tsum_principalPart` target.
  -/
  h_Btr_opposite_principalPart :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        Btr
        W.s0
        (-(groupedResidueCoeff M (pairGroupedPoleClass M W)))

  /--
  Regularity away from witness pole points.
  -/
  h_Btr_regular_away_from_witnesses :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC Btr z


/--
If the corrected prime-side transform is chosen to be `D.B`, the alignment
contract reduces to two precise mathematical obligations:

1. `D.B` has the required opposite principal parts at witness pole points.
2. `D.B` is regular away from witness pole points.

This is the D-route adapter. It does not claim those two facts; it names
exactly what must be proved if `OperatorResolventBridge.B` is the intended
transformed prime-side object.
-/
def primeSideAlignmentContract_of_D_B
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (hPP :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          D.B
          W.s0
          (-(groupedResidueCoeff M (pairGroupedPoleClass M W))))
    (hReg :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC D.B z) :
    PrimeSideAlignmentContract M D :=
  { Btr := D.B
    h_Btr_matches_D_on_overlap := by
      intro s hs
      rfl
    h_Btr_opposite_principalPart := hPP
    h_Btr_regular_away_from_witnesses := hReg }

#check primeSideAlignmentContract_of_D_B

#check PrimeSideAlignmentContract
#check OperatorResolventBridge
#check RH_from_designed_D_zero_density_localEF_noBregular

end

end RHFormalization
