import RHFormalization.CanonicalPrimePowerConcreteTsumPackage

/-!
# RHFormalization.CanonicalPrimePowerSummabilityMajorant

Majorant-level summability for the canonical prime-power package.

This is not an RH endpoint.

The previous layer defined the shared canonical package as the `tsum`

  ∑' q : PrimePowerPair, q.weightC * Kshared q.center s

and still required direct complex summability of that term sequence.

This file reduces that summability requirement to a standard norm-majorant
statement:

  ‖q.weightC * Kshared q.center s‖ ≤ majorant q,

where the real majorant is summable.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators


/--
Majorant-level data for the concrete canonical prime-power package.

Compared with `CanonicalPrimePowerConcreteTsumKernelSeriesData`, this replaces

  `h_summable`

by the more concrete estimate package:

* a nonnegative real majorant;
* a pointwise norm bound by that majorant;
* summability of the majorant.
-/
structure CanonicalPrimePowerMajorantKernelSeriesData
    (X : DFiniteStagePackageFromOperatorLayer) where
  alpha : ℕ → DFiniteStage

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

  /-- Real nonnegative majorant for the shared prime-power kernel terms. -/
  majorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the majorant. -/
  h_majorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ majorant q

  /--
  Pointwise norm bound for the prime-power kernel term on the D overlap
  half-plane.
  -/
  h_term_norm_le_majorant :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ q : PrimePowerPair,
        ‖q.weightC * Kshared q.center s‖ ≤ majorant q

  /-- Summability of the real majorant. -/
  h_majorant_summable :
    Summable majorant

  /--
  The finite weighted canonical partial sums converge to the shared package.

  This is the support-aware replacement for full raw `PrimePowerPair`
  exhaustion. It is carried as data here because summability plus valid-index
  eventual containment alone does not imply raw finite-set exhaustion.
  -/
  h_weighted_partial_tendsto :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 ((canonicalPrimePowerPackageFromKernelTsum
              X.toStagePackage.sigma0
              Kshared).Bshared s))

/--
Convert majorant-level data into the previous concrete tsum-kernel data.

This discharges the complex summability field using the norm-majorant estimate.
-/
def CanonicalPrimePowerMajorantKernelSeriesData.toConcreteTsumKernelSeriesData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerMajorantKernelSeriesData X) :
    CanonicalPrimePowerConcreteTsumKernelSeriesData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    h_kernel_agrees_on_indices := S.h_kernel_agrees_on_indices
    h_weighted_partial_tendsto := S.h_weighted_partial_tendsto
    h_summable := by
      intro s hs

      have hnorm :
          Summable
            (fun q : PrimePowerPair =>
              ‖q.weightC * S.Kshared q.center s‖) :=
        Summable.of_nonneg_of_le
          (fun q : PrimePowerPair =>
            norm_nonneg (q.weightC * S.Kshared q.center s))
          (fun q : PrimePowerPair =>
            S.h_term_norm_le_majorant s hs q)
          S.h_majorant_summable

      exact hnorm.of_norm }

/--
Build `CanonicalPrimePowerExhaustionData` from majorant-level data.
-/
def CanonicalPrimePowerMajorantKernelSeriesData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerMajorantKernelSeriesData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toConcreteTsumKernelSeriesData.toExhaustionData

/--
Build `DBcanLimitData` directly from majorant-level canonical prime-power data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerMajorantKernelSeries
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerMajorantKernelSeriesData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerConcreteTsumKernelSeries
    X
    S.toConcreteTsumKernelSeriesData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once the majorant-level data is supplied.
-/
theorem canonicalPrimePowerMajorantKernelSeries_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerMajorantKernelSeriesData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerMajorantKernelSeries X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerConcreteTsumKernelSeries_h_Bcan_matches_tsum
      X
      S.toConcreteTsumKernelSeriesData
      s
      hs

end

end RHFormalization
