import RHFormalization.HMeromorphicWithNormalFormChosenCshared

/-!
# RHFormalization.HExplicitFormulaSplit

This file removes the H-side split identity as an independent input by defining

  Harch s := Y.B.Cshared.Bshared s + Zpole s.

Then

  Y.B.Cshared.Bshared s = Harch s - Zpole s

is algebraic.

The remaining real analytic input becomes the holomorphy/cancellation theorem:

  HolomorphicOnC (fun s => Y.B.Cshared.Bshared s + Zpole s) Ω.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The H-archimedean package built from the explicit-formula split expression

  Harch = Bshared + Zpole.
-/
def HarchPackageFromBsharedAddZpole
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (h_Harch_holo :
      HolomorphicOnC
        (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
        Ω) :
    HArchPackage :=
{ Harch := fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s
  h_Harch_holo := h_Harch_holo }

/--
If `Harch` is defined as `Bshared + Zpole`, then the H-side split identity
is immediate.
-/
theorem HarchPackageFromBsharedAddZpole_split
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (h_Harch_holo :
      HolomorphicOnC
        (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
        Ω)
    (sigma0 : ℝ) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane sigma0 →
        Y.B.Cshared.Bshared s =
          (HarchPackageFromBsharedAddZpole Y Zpole h_Harch_holo).Harch s
            - Zpole s := by
  intro s _hs
  simp [HarchPackageFromBsharedAddZpole]

/--
Final RH spine with `Harch` constructed as `Bshared + Zpole`.

This replaces the explicit `h_split` input by the real analytic holomorphy
input for the cancellation expression.
-/
theorem finalRHSpine_from_explicitFormulaHarch
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M E Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M E Zpole)
    (sigma0 : ℝ)
    (h_Cshared_sigma_le : Y.B.Cshared.sigma0 ≤ sigma0)
    (h_Harch_holo :
      HolomorphicOnC
        (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
        Ω)
    (h_genuine_poles :
      ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0)
    (normalFormGroupedLayer :
      HSideGroupedPoleNormalFormData
        (buildZeroPolePackageFromHMeromorphicLayer
          (buildHMeromorphicPackageLayerWithChosenCshared
            M E Zpole convergence poleSeriesMeromorphic
            (HarchPackageFromBsharedAddZpole Y Zpole h_Harch_holo)
            Y.B.Cshared
            sigma0
            h_Cshared_sigma_le
            (HarchPackageFromBsharedAddZpole_split
              Y Zpole h_Harch_holo sigma0)
            h_genuine_poles))) :
    RiemannHypothesis :=
  finalRHSpine_from_HChosenDSharedC
    ZF
    Y
    M
    E
    Zpole
    convergence
    poleSeriesMeromorphic
    (HarchPackageFromBsharedAddZpole Y Zpole h_Harch_holo)
    sigma0
    h_Cshared_sigma_le
    (HarchPackageFromBsharedAddZpole_split
      Y Zpole h_Harch_holo sigma0)
    h_genuine_poles
    normalFormGroupedLayer

end

end RHFormalization
