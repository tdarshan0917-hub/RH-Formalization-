import RHFormalization.HMeromorphicLayerChosenCshared
import RHFormalization.AppendixESharedPackageFunctionalCompatibility

/-!
# RHFormalization.HMeromorphicWithNormalFormChosenCshared

Build a full `HMeromorphicWithNormalFormPoles` package whose H-overlap
`Cshared` is a chosen canonical package.

This is the final packaging step after `HMeromorphicLayerChosenCshared`.
It moves the chosen-Cshared equality from the H layer to the full H package
used by the final RH spine.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build a full H package with normal-form poles from a chosen-Cshared H layer and
the required grouped normal-form data.

The overlap package inside the resulting `X` uses the chosen package `C`.
-/
def buildHMeromorphicWithNormalFormPolesWithChosenCshared
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
      ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            M E Zpole convergence poleSeriesMeromorphic HarchPackage
            C sigma0 h_Cshared_sigma_le h_split h_genuine_poles))) :
    HMeromorphicWithNormalFormPoles :=
{ layer :=
    buildHMeromorphicPackageLayerWithChosenCshared
      M E Zpole convergence poleSeriesMeromorphic HarchPackage
      C sigma0 h_Cshared_sigma_le h_split h_genuine_poles
  normalFormGroupedLayer := normalFormGroupedLayer }

/--
The full H package built with chosen `Cshared` has that exact H-overlap
`Cshared`.
-/
theorem buildHMeromorphicWithNormalFormPolesWithChosenCshared_Cshared_eq
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
      ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            M E Zpole convergence poleSeriesMeromorphic HarchPackage
            C sigma0 h_Cshared_sigma_le h_split h_genuine_poles))) :
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M E Zpole convergence poleSeriesMeromorphic HarchPackage
      C sigma0 h_Cshared_sigma_le h_split h_genuine_poles
      normalFormGroupedLayer).layer.overlap.Cshared = C := by
  rfl

/--
Final RH spine when the H package is built with the D-side shared canonical
package.

This is the useful top-level specialization: choose `C := Y.B.Cshared`, then the
Cshared equality required by `finalRHSpine_from_Cshared_eq` is automatic.
-/
theorem finalRHSpine_from_HChosenDSharedC
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M E Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M E Zpole)
    (HarchPackage : HArchPackage)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : Y.B.Cshared.sigma0 ≤ sigma0)
    (h_split :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigma0 →
          Y.B.Cshared.Bshared s = HarchPackage.Harch s - Zpole s)
    (h_genuine_poles :
      ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            M E Zpole convergence poleSeriesMeromorphic HarchPackage
            Y.B.Cshared sigma0 h_Cshared_sigma_le h_split h_genuine_poles))) :
    RiemannHypothesis := by
  let X :=
    buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M E Zpole convergence poleSeriesMeromorphic HarchPackage
      Y.B.Cshared sigma0 h_Cshared_sigma_le h_split h_genuine_poles
      normalFormGroupedLayer
  exact
    finalRHSpine_from_Cshared_eq
      ZF
      Y
      X
      (by rfl)

end

end RHFormalization
