import RHFormalization.HSideOverlapChosenCshared

/-!
# RHFormalization.HMeromorphicLayerChosenCshared

Build an H-meromorphic package layer whose overlap package uses a chosen
canonical prime-power package.

This is not an RH endpoint. It wires the chosen-Cshared overlap into the actual
H layer object used by `HMeromorphicWithNormalFormPoles`.

The remaining hard H/E input is the split identity:

  C.Bshared s = Harch s - Zpole s

on the overlap half-plane.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build an H package layer using a chosen canonical shared package `C`.

The overlap field is built by `buildHSideOverlapPackageWithChosenCshared`, so
its `Cshared` field is definitionally the chosen package.
-/
def buildHMeromorphicPackageLayerWithChosenCshared
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M E Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M E Zpole)
    (HarchPackage : HArchPackage)
    (C : CanonicalPrimePowerPackage)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : C.sigma0 ≤ sigma0)
    (h_split :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigma0 →
          C.Bshared s = HarchPackage.Harch s - Zpole s)
    (h_genuine_poles :
      ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0) :
    HMeromorphicPackageLayerV2 :=
{ M := M
  E := E
  Zpole := Zpole
  convergence := convergence
  poleSeriesMeromorphic := poleSeriesMeromorphic
  HarchPackage := HarchPackage
  overlap :=
    buildHSideOverlapPackageWithChosenCshared
      Zpole
      HarchPackage.Harch
      C
      sigma0
      h_Cshared_sigma_le
      h_split
  h_genuine_poles := h_genuine_poles }

/--
The H layer built with a chosen `Cshared` has that exact overlap `Cshared`.
-/
theorem buildHMeromorphicPackageLayerWithChosenCshared_Cshared_eq
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M E Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M E Zpole)
    (HarchPackage : HArchPackage)
    (C : CanonicalPrimePowerPackage)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : C.sigma0 ≤ sigma0)
    (h_split :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigma0 →
          C.Bshared s = HarchPackage.Harch s - Zpole s)
    (h_genuine_poles :
      ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0) :
    (buildHMeromorphicPackageLayerWithChosenCshared
      M E Zpole convergence poleSeriesMeromorphic HarchPackage
      C sigma0 h_Cshared_sigma_le h_split h_genuine_poles).overlap.Cshared
      = C := by
  rfl

end

end RHFormalization
