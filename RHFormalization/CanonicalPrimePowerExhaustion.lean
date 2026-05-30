import RHFormalization.AppendixDPrimePowerLimitReduction

/-!
# RHFormalization.CanonicalPrimePowerExhaustion

Canonical prime-power finite-exhaustion data.

This file is not an RH endpoint.

It names the exact remaining D-side convergence input after the finite spike-sum
formula has already been extracted from the operator layer.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Finite-exhaustion data for the canonical prime-power package along the D-side
finite operator stages.

This is the precise convergence theorem still needed from Appendix D/H package
construction:

finite canonical prime-power packages
  `finiteCanonicalPrimePowerPackage ...`
converge pointwise on the D overlap half-plane to the shared package `C.Bshared`.
-/
structure CanonicalPrimePowerExhaustionData
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage

  /--
  The shared package is legal on the D-side overlap half-plane.
  -/
  h_Cshared_sigma_le :
    C.sigma0 ≤ X.toStagePackage.sigma0

  /--
  Main remaining convergence theorem.
  -/
  h_tendsto :
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
Convert canonical prime-power exhaustion data into the D-side reduced convergence
object already consumed by the D construction.
-/
def CanonicalPrimePowerExhaustionData.toDOperatorFiniteCanonicalLimit
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (E : CanonicalPrimePowerExhaustionData X C) :
    DOperatorFiniteCanonicalLimitAtOverlapData X C :=
  { alpha := E.alpha
    h_Cshared_sigma_le := E.h_Cshared_sigma_le
    h_finiteCanonical_tendsto_Bshared := E.h_tendsto }

/--
Build `DBcanLimitData` directly from canonical prime-power exhaustion data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerExhaustion
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (E : CanonicalPrimePowerExhaustionData X C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
    X
    C
    E.toDOperatorFiniteCanonicalLimit

/--
The D-side canonical package agrees with the shared package once canonical
prime-power exhaustion data is supplied.
-/
theorem canonicalPrimePowerExhaustion_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (E : CanonicalPrimePowerExhaustionData X C)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerExhaustion X C E).Bcan s =
      C.Bshared s := by
  exact
    (buildDBcanLimitDataFromCanonicalPrimePowerExhaustion X C E).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
