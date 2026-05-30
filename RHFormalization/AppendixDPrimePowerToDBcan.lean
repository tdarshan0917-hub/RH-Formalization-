import RHFormalization.AppendixDPrimePowerLimitComparison

/-!
# RHFormalization.AppendixDPrimePowerToDBcan

Builds the strengthened `DBcanLimitData` object from the finite-stage
prime-power formula and the finite-to-limit comparison data.

This is not an RH endpoint.

It is the D-side construction bridge:

finite formula + convergence
  ⇒ `Bcan = Cshared.Bshared` on the D overlap half-plane.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
D-side prime-power limit data stated exactly on the package overlap half-plane
`RightHalfPlane P.sigma0`.

This is the version directly usable for constructing `DBcanLimitData P`.
-/
structure DPrimePowerLimitAtOverlapData
    (P : DFiniteStagePackage)
    (F : DFiniteStageCanonicalPrimePowerFormula P)
    (Bcan : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage

  /--
  The shared package is already convergent/legal on the D overlap half-plane.
  -/
  h_Cshared_sigma_le :
    C.sigma0 ≤ P.sigma0

  /--
  D finite packages converge pointwise on the D overlap half-plane.
  -/
  h_B_stage_tendsto_Bcan :
    ∀ s : ℂ, s ∈ RightHalfPlane P.sigma0 →
      Tendsto
        (fun n : ℕ => P.B_stage (alpha n) s)
        Filter.atTop
        (𝓝 (Bcan s))

  /--
  The finite canonical prime-power packages converge to the shared package
  pointwise on the D overlap half-plane.
  -/
  h_finiteCanonical_tendsto_Bshared :
    ∀ s : ℂ, s ∈ RightHalfPlane P.sigma0 →
      Tendsto
        (fun n : ℕ =>
          finiteCanonicalPrimePowerPackage
            (F.indices (alpha n))
            (F.kernel (alpha n))
            s)
        Filter.atTop
        (𝓝 (C.Bshared s))

/--
The D-side package limit equals the shared canonical package on the D overlap
half-plane.
-/
theorem DPrimePowerLimitAtOverlapData.h_Bcan_eq_shared
    {P : DFiniteStagePackage}
    {F : DFiniteStageCanonicalPrimePowerFormula P}
    {Bcan : ℂ → ℂ}
    {C : CanonicalPrimePowerPackage}
    (L : DPrimePowerLimitAtOverlapData P F Bcan C) :
    ∀ s : ℂ, s ∈ RightHalfPlane P.sigma0 →
      Bcan s = C.Bshared s := by
  exact
    F.limit_eq_shared
      L.alpha
      Bcan
      C.Bshared
      P.sigma0
      L.h_B_stage_tendsto_Bcan
      L.h_finiteCanonical_tendsto_Bshared

/--
Construct the strengthened `DBcanLimitData` from finite-stage formula and
overlap convergence data.
-/
def buildDBcanLimitDataFromPrimePowerLimit
    (P : DFiniteStagePackage)
    (F : DFiniteStageCanonicalPrimePowerFormula P)
    (Bcan : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage)
    (L : DPrimePowerLimitAtOverlapData P F Bcan C) :
    DBcanLimitData P :=
  { Bcan := Bcan
    Cshared := C
    h_Cshared_sigma_le := L.h_Cshared_sigma_le
    h_Bcan_matches_shared := L.h_Bcan_eq_shared }

end

end RHFormalization
