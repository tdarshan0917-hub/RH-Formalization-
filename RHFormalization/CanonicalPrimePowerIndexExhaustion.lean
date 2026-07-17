import RHFormalization.CanonicalPrimePowerKernelSeries

/-!
# RHFormalization.CanonicalPrimePowerIndexExhaustion

Concrete index-exhaustion layer for the canonical prime-power series.

This is not an RH endpoint.

The previous file reduced the D/H finite-to-limit burden to kernel-level series
data with three fields:

* finite index exhaustion as `Tendsto ... atTop atTop`;
* stage-kernel agreement on finite indices;
* `HasSum` of the infinite shared prime-power series.

This file removes the abstract `Finset`-filter exhaustion field by proving it
from the concrete cutoff statement:

  every prime-power index eventually belongs to the finite stage index set.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If every index eventually belongs to the finite index sets, then the finite index
sets tend to `atTop` in the `Finset` order.

This is the standard finite-set exhaustion principle.
-/
theorem finset_tendsto_atTop_of_eventually_mem
    {ι : Type*}
    [DecidableEq ι]
    (I : ℕ → Finset ι)
    (hmem : ∀ q : ι, ∀ᶠ n in Filter.atTop, q ∈ I n) :
    Tendsto I Filter.atTop (Filter.atTop : Filter (Finset ι)) := by
  classical
  refine tendsto_atTop.2 ?_
  intro S
  refine S.induction_on ?h_empty ?h_insert
  · exact Filter.Eventually.of_forall (fun n => by
      intro q hq
      have hfalse : False := by
        simpa using hq
      exact False.elim hfalse)
  · intro a S ha hS
    filter_upwards [hmem a, hS] with n haI hSI q hq
    simp only [Finset.mem_insert] at hq
    rcases hq with hqa | hqS
    · simpa [hqa] using haI
    · exact hSI hqS

/--
A more concrete form of index exhaustion.

Instead of asking directly for

  `Tendsto indices atTop atTop`,

we ask for the natural finite-cutoff statement:

  every prime-power pair appears in all sufficiently large finite stages.
-/
structure CanonicalPrimePowerIndexKernelSeriesData
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
      IsPrimePowerPair q →
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
  The finite weighted canonical partial sums converge to the shared package.

  This is the support-aware replacement for full raw `PrimePowerPair`
  exhaustion.
  -/
  h_weighted_partial_tendsto :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 (C.Bshared s))

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
Convert concrete index-exhaustion data into the previous kernel-series data.

This discharges the abstract `h_indices_tendsto_top` field from the concrete
eventual-membership cutoff condition.
-/
def CanonicalPrimePowerIndexKernelSeriesData.toKernelSeriesData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerIndexKernelSeriesData X C) :
    CanonicalPrimePowerKernelSeriesData X C :=
  { alpha := S.alpha
    h_Cshared_sigma_le := S.h_Cshared_sigma_le
    Kshared := S.Kshared
    h_weighted_partial_tendsto := S.h_weighted_partial_tendsto
    h_kernel_agrees_on_indices := S.h_kernel_agrees_on_indices
    h_hasSum := S.h_hasSum }

/--
Build `CanonicalPrimePowerExhaustionData` from concrete index-exhaustion
kernel-series data.
-/
def CanonicalPrimePowerIndexKernelSeriesData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerIndexKernelSeriesData X C) :
    CanonicalPrimePowerExhaustionData X C :=
  S.toKernelSeriesData.toExhaustionData

/--
Build `DBcanLimitData` directly from concrete index-exhaustion kernel-series
data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerIndexKernelSeries
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerIndexKernelSeriesData X C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerKernelSeries
    X
    C
    S.toKernelSeriesData

/--
The D-side canonical package matches the shared canonical package once concrete
index-exhaustion kernel-series data is supplied.
-/
theorem canonicalPrimePowerIndexKernelSeries_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerIndexKernelSeriesData X C)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerIndexKernelSeries X C S).Bcan s =
      C.Bshared s := by
  exact
    (buildDBcanLimitDataFromCanonicalPrimePowerIndexKernelSeries X C S).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
