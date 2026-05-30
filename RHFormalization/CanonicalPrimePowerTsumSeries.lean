import RHFormalization.CanonicalPrimePowerIndexExhaustion

/-!
# RHFormalization.CanonicalPrimePowerTsumSeries

Tsum-level realization of the canonical prime-power package.

This is not an RH endpoint.

The previous layer reduced the D/H finite-to-limit burden to:

* concrete finite index exhaustion;
* stage-kernel agreement on finite indices;
* `HasSum` of the infinite shared prime-power series.

This file removes the abstract `HasSum` input and replaces it by two sharper
pieces:

* summability of the shared prime-power kernel series;
* identification of `C.Bshared` with the corresponding `tsum`.

This is a real reduction of the analytic package obligation.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Tsum-level canonical prime-power series data.

Compared with `CanonicalPrimePowerIndexKernelSeriesData`, this replaces

  `h_hasSum`

by

  `h_summable` and `h_Bshared_eq_tsum`.

Thus the remaining analytic work is closer to standard Mathlib summability and
the manuscript's explicit definition of the shared canonical package.
-/
structure CanonicalPrimePowerTsumKernelSeriesData
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage

  /-- The shared package is legal on the D-side overlap half-plane. -/
  h_Cshared_sigma_le :
    C.sigma0 ≤ X.toStagePackage.sigma0

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  Concrete finite-stage exhaustion: every prime-power index eventually appears
  in the finite stage index sets.
  -/
  h_indices_eventually_contains :
    ∀ q : PrimePowerPair,
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /--
  On each finite stage index set, the stage kernel agrees with the shared kernel.
  -/
  h_kernel_agrees_on_indices :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        ∀ s : ℂ,
          X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
            Kshared q.center s

  /--
  Summability of the infinite shared prime-power kernel series on the D overlap
  half-plane.
  -/
  h_summable :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Summable
        (fun q : PrimePowerPair => q.weightC * Kshared q.center s)

  /--
  The shared canonical package is represented by the `tsum` of the infinite
  prime-power kernel series on the D overlap half-plane.
  -/
  h_Bshared_eq_tsum :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      C.Bshared s =
        ∑' q : PrimePowerPair,
          q.weightC * Kshared q.center s

/--
Convert tsum-level data into the previous index/kernel series data.

The `HasSum` field is now derived from summability plus the `Bshared = tsum`
representation.
-/
def CanonicalPrimePowerTsumKernelSeriesData.toIndexKernelSeriesData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerTsumKernelSeriesData X C) :
    CanonicalPrimePowerIndexKernelSeriesData X C :=
  { alpha := S.alpha
    h_Cshared_sigma_le := S.h_Cshared_sigma_le
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    h_kernel_agrees_on_indices := S.h_kernel_agrees_on_indices
    h_hasSum := by
      intro s hs
      have hsum :
          HasSum
            (fun q : PrimePowerPair => q.weightC * S.Kshared q.center s)
            (∑' q : PrimePowerPair,
              q.weightC * S.Kshared q.center s) :=
        (S.h_summable s hs).hasSum

      simpa [S.h_Bshared_eq_tsum s hs] using hsum }

/--
Build `CanonicalPrimePowerExhaustionData` from tsum-level kernel series data.
-/
def CanonicalPrimePowerTsumKernelSeriesData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerTsumKernelSeriesData X C) :
    CanonicalPrimePowerExhaustionData X C :=
  S.toIndexKernelSeriesData.toExhaustionData

/--
Build `DBcanLimitData` directly from tsum-level canonical prime-power series
data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerTsumKernelSeries
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerTsumKernelSeriesData X C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerIndexKernelSeries
    X
    C
    S.toIndexKernelSeriesData

/--
The D-side canonical package matches the shared canonical package once the
tsum-level kernel-series realization is supplied.
-/
theorem canonicalPrimePowerTsumKernelSeries_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerTsumKernelSeriesData X C)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerTsumKernelSeries X C S).Bcan s =
      C.Bshared s := by
  exact
    (buildDBcanLimitDataFromCanonicalPrimePowerTsumKernelSeries X C S).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
