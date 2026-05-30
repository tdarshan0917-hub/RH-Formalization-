import RHFormalization.AppendixDOperatorPrimePowerToDBcan

/-!
# RHFormalization.AppendixDPrimePowerLimitReduction

Reduces the D-side prime-power limit input.

This is not an RH endpoint.

Since the finite operator layer already proves

  `P.B_stage α s =
    finiteCanonicalPrimePowerPackage (F.indices α) (F.kernel α) s`,

the convergence of `P.B_stage (alpha n) s` follows from convergence of the
finite canonical prime-power packages, once we choose

  `Bcan := C.Bshared`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
The remaining operator-layer finite-canonical convergence data.

This is the genuinely analytic D-side convergence obligation after the finite
spike-sum formula has been theorem-backed.
-/
structure DOperatorFiniteCanonicalLimitAtOverlapData
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage

  /--
  The shared canonical package is legal on the D overlap half-plane.
  -/
  h_Cshared_sigma_le :
    C.sigma0 ≤ X.toStagePackage.sigma0

  /--
  The finite canonical prime-power packages converge to the shared package on
  the D overlap half-plane.
  -/
  h_finiteCanonical_tendsto_Bshared :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          finiteCanonicalPrimePowerPackage
            (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
            (X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n))
            s)
        Filter.atTop
        (𝓝 (C.Bshared s))

/--
Build the full operator prime-power limit data from the single finite-canonical
convergence theorem.

The `B_stage` convergence field is derived from the already-proved finite-stage
canonical formula.
-/
def buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData X C) :
    DOperatorPrimePowerLimitAtOverlapData X C.Bshared C :=
  { alpha := L.alpha
    h_Cshared_sigma_le := L.h_Cshared_sigma_le
    h_B_stage_tendsto_Bcan := by
      intro s hs

      have hcanon :=
        L.h_finiteCanonical_tendsto_Bshared s hs

      have hseq :
          (fun n : ℕ => X.toStagePackage.B_stage (L.alpha n) s)
            =
          (fun n : ℕ =>
            finiteCanonicalPrimePowerPackage
              (X.toFiniteCanonicalPrimePowerFormula.indices (L.alpha n))
              (X.toFiniteCanonicalPrimePowerFormula.kernel (L.alpha n))
              s) := by
        funext n
        exact
          X.toFiniteCanonicalPrimePowerFormula.h_B_stage_eq_finiteCanonical
            (L.alpha n)
            s

      simpa [hseq] using hcanon

    h_finiteCanonical_tendsto_Bshared :=
      L.h_finiteCanonical_tendsto_Bshared }

/--
Directly build `DBcanLimitData` from the reduced one-convergence D-side input.
-/
def buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData X C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromOperatorPrimePowerLimit
    X
    C.Bshared
    C
    (buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit X C L)

/--
The D-side package now matches the shared canonical package from the reduced
finite-canonical convergence input.
-/
theorem finiteCanonicalLimit_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (L : DOperatorFiniteCanonicalLimitAtOverlapData X C)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    C.Bshared s =
      (buildDBcanLimitDataFromOperatorFiniteCanonicalLimit X C L).Cshared.Bshared s := by
  rfl

end

end RHFormalization
