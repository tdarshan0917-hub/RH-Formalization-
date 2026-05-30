import RHFormalization.CanonicalPrimePowerSeries

/-!
# RHFormalization.CanonicalPrimePowerKernelSeries

Kernel-level realization of the canonical prime-power series data.

This is not an RH endpoint.

The previous layer, `CanonicalPrimePowerSeriesData`, reduced the D-side
finite-to-limit package to three concrete ingredients:

* finite index exhaustion;
* identification of finite canonical packages with partial sums;
* `HasSum` of the infinite shared prime-power series.

This file proves the finite-package/partial-sum identification from the concrete
definition of `finiteCanonicalPrimePowerPackage`, assuming the stage kernels
agree with one shared kernel on the finite stage index sets.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Kernel-level data realizing the shared canonical prime-power package.

The key improvement over `CanonicalPrimePowerSeriesData` is that
`h_finite_eq_partial` is no longer an arbitrary field. It is proved by unfolding
`finiteCanonicalPrimePowerPackage`, using `h_kernel_agrees_on_indices`.
-/
structure CanonicalPrimePowerKernelSeriesData
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage

  /-- The shared package is legal on the D-side overlap half-plane. -/
  h_Cshared_sigma_le :
    C.sigma0 ≤ X.toStagePackage.sigma0

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  The finite prime-power index sets from the operator formula exhaust the full
  prime-power index type.
  -/
  h_indices_tendsto_top :
    Tendsto
      (fun n : ℕ =>
        X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
      Filter.atTop
      (Filter.atTop : Filter (Finset PrimePowerPair))

  /--
  On each finite stage index set, the stage kernel agrees with the shared kernel.
  This is the remaining finite-stage kernel-identification theorem.
  -/
  h_kernel_agrees_on_indices :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        ∀ s : ℂ,
          X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
            Kshared q.center s

  /--
  The infinite shared prime-power series has sum `C.Bshared` on the D overlap
  half-plane.
  -/
  h_hasSum :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      HasSum
        (fun q : PrimePowerPair => q.weightC * Kshared q.center s)
        (C.Bshared s)

/--
Convert kernel-level series data into the previous `CanonicalPrimePowerSeriesData`.

This proves the finite package equals the partial sum by unfolding
`finiteCanonicalPrimePowerPackage` and using finite-sum congruence.
-/
def CanonicalPrimePowerKernelSeriesData.toSeriesData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerKernelSeriesData X C) :
    CanonicalPrimePowerSeriesData X C :=
  { alpha := S.alpha
    h_Cshared_sigma_le := S.h_Cshared_sigma_le
    term := fun q s => q.weightC * S.Kshared q.center s
    h_indices_tendsto_top := S.h_indices_tendsto_top
    h_finite_eq_partial := by
      intro n s
      change
        finiteCanonicalPrimePowerPackage
            (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n))
            (X.toFiniteCanonicalPrimePowerFormula.kernel (S.alpha n))
            s =
          (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n)).sum
            (fun q : PrimePowerPair => q.weightC * S.Kshared q.center s)
      dsimp [finiteCanonicalPrimePowerPackage]
      exact
        Finset.sum_congr rfl
          (fun q hq => by
            rw [S.h_kernel_agrees_on_indices n q hq s])
    h_hasSum := S.h_hasSum }

/--
Build `CanonicalPrimePowerExhaustionData` from kernel-level series data.
-/
def CanonicalPrimePowerKernelSeriesData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerKernelSeriesData X C) :
    CanonicalPrimePowerExhaustionData X C :=
  S.toSeriesData.toExhaustionData

/--
Build `DBcanLimitData` directly from kernel-level canonical prime-power series
data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerKernelSeries
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerKernelSeriesData X C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerSeries
    X
    C
    S.toSeriesData

/--
The D-side canonical package matches the shared canonical package once the
kernel-level series realization is supplied.
-/
theorem canonicalPrimePowerKernelSeries_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerKernelSeriesData X C)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerKernelSeries X C S).Bcan s =
      C.Bshared s := by
  exact
    (buildDBcanLimitDataFromCanonicalPrimePowerKernelSeries X C S).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
