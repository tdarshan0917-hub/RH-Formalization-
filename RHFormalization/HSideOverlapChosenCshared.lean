import RHFormalization.AppendixESharedPackageCompatibility

/-!
# RHFormalization.HSideOverlapChosenCshared

Construct an H-side overlap package using a chosen canonical prime-power package.

This is a targeted Appendix-E/H-side reduction.  It makes the H-side
`overlap.Cshared` definitionally equal to the chosen package `C`.

The remaining mathematical input is then the true split identity:

  C.Bshared s = Harch s - Zpole s

on the overlap half-plane.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build an H-side overlap package whose `Cshared` is the chosen package `C`.

The `h_Bzero_matches_shared` field is automatic because we set
`Bzero := C.Bshared`.

The only real H/E analytic input is `h_split`.
-/
def buildHSideOverlapPackageWithChosenCshared
    (Zpole Harch : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : C.sigma0 ≤ sigma0)
    (h_split :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigma0 →
          C.Bshared s = Harch s - Zpole s) :
    HSideOverlapPackage Zpole Harch :=
{ Bzero := C.Bshared
  sigma0 := sigma0
  Cshared := C
  h_Cshared_sigma_le := h_Cshared_sigma_le
  h_Bzero_matches_shared := by
    intro s hs
    rfl
  h_split := h_split }

/--
The overlap package built with a chosen `Cshared` has exactly that `Cshared`.
-/
theorem buildHSideOverlapPackageWithChosenCshared_Cshared_eq
    (Zpole Harch : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : C.sigma0 ≤ sigma0)
    (h_split :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigma0 →
          C.Bshared s = Harch s - Zpole s) :
    (buildHSideOverlapPackageWithChosenCshared
      Zpole Harch C sigma0 h_Cshared_sigma_le h_split).Cshared = C := by
  rfl

end

end RHFormalization
