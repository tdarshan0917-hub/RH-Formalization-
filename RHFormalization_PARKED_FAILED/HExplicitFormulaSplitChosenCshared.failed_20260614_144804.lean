import RHFormalization.HSideOverlapChosenCshared
import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.ZpoleFromSeries

/-!
# RHFormalization.HExplicitFormulaSplitChosenCshared

This is the non-looping H-side split.

It does not mention `designedY`.
It does not use the old displacement kernel.
It works for any chosen canonical prime package `C`.

If `C.Bshared + Zpole` is holomorphic on Ω, define

  Harch := C.Bshared + Zpole.

Then the Appendix-H overlap split

  C.Bshared = Harch - Zpole

is tautological by ring.

This is the correct generic H-side wrapper for the shifted/Laplace package.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- Build the archimedean/H package from an arbitrary chosen shared package. -/
def HarchPackageFromChosenCsharedAddZpole
    (C : CanonicalPrimePowerPackage)
    (Zpole : ℂ → ℂ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => C.Bshared s + Zpole s)
        Ω) :
    HArchPackage :=
  { Harch := fun s : ℂ => C.Bshared s + Zpole s
    h_Harch_holo := h_holo }

/-- The chosen-Cshared split is tautological once Harch is defined as C+B. -/
theorem HarchPackageFromChosenCsharedAddZpole_split
    (C : CanonicalPrimePowerPackage)
    (Zpole : ℂ → ℂ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => C.Bshared s + Zpole s)
        Ω)
    (sigma0 : ℝ)
    (s : ℂ) :
    s ∈ RightHalfPlane sigma0 →
      C.Bshared s =
        (HarchPackageFromChosenCsharedAddZpole C Zpole h_holo).Harch s
          - Zpole s := by
  intro _hs
  simp [HarchPackageFromChosenCsharedAddZpole]
  ring

/-- Build the H-side overlap package for any chosen C from holomorphy of C+B. -/
def buildHSideOverlapPackageFromChosenCsharedHolo
    (C : CanonicalPrimePowerPackage)
    (Zpole : ℂ → ℂ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => C.Bshared s + Zpole s)
        Ω)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : C.sigma0 ≤ sigma0) :
    HSideOverlapPackage Zpole
      (HarchPackageFromChosenCsharedAddZpole C Zpole h_holo).Harch :=
  buildHSideOverlapPackageWithChosenCshared
    Zpole
    (HarchPackageFromChosenCsharedAddZpole C Zpole h_holo).Harch
    C
    sigma0
    h_Cshared_sigma_le
    (HarchPackageFromChosenCsharedAddZpole_split C Zpole h_holo sigma0)

/-- The overlap package really uses the chosen Cshared. -/
theorem buildHSideOverlapPackageFromChosenCsharedHolo_Cshared_eq
    (C : CanonicalPrimePowerPackage)
    (Zpole : ℂ → ℂ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => C.Bshared s + Zpole s)
        Ω)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : C.sigma0 ≤ sigma0) :
    (buildHSideOverlapPackageFromChosenCsharedHolo
      C Zpole h_holo sigma0 h_Cshared_sigma_le).Cshared = C := by
  rfl

/-- Specialization to the shifted/Laplace package. This is the real h_holo target. -/
def shiftedLaplaceHarchPackageFromHolo
    (sigma0 : ℝ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    HArchPackage :=
  HarchPackageFromChosenCsharedAddZpole
    (shiftedLaplacePrimePackageAt sigma0)
    (ZpoleSeries defaultZeroMultiplicityData)
    h_holo

/-- Shifted/Laplace explicit-formula split, once its holomorphy is proved. -/
theorem shiftedLaplaceHarchPackageFromHolo_split
    (sigma0 : ℝ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω)
    (s : ℂ) :
    s ∈ RightHalfPlane sigma0 →
      (shiftedLaplacePrimePackageAt sigma0).Bshared s =
        (shiftedLaplaceHarchPackageFromHolo sigma0 h_holo).Harch s
          - ZpoleSeries defaultZeroMultiplicityData s := by
  intro hs
  exact
    HarchPackageFromChosenCsharedAddZpole_split
      (shiftedLaplacePrimePackageAt sigma0)
      (ZpoleSeries defaultZeroMultiplicityData)
      h_holo
      sigma0
      s
      hs

#print axioms HarchPackageFromChosenCsharedAddZpole
#print axioms HarchPackageFromChosenCsharedAddZpole_split
#print axioms buildHSideOverlapPackageFromChosenCsharedHolo
#print axioms buildHSideOverlapPackageFromChosenCsharedHolo_Cshared_eq
#print axioms shiftedLaplaceHarchPackageFromHolo
#print axioms shiftedLaplaceHarchPackageFromHolo_split

end

end RHFormalization
