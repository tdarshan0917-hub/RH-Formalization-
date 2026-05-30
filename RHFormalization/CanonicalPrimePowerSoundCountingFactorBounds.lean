import RHFormalization.CanonicalPrimePowerCountWeightProductBound

/-!
# RHFormalization.CanonicalPrimePowerSoundCountingFactorBounds

Factor-bound version of the sound counting D-window package.

This version intentionally removes the artificial `numeratorBound` layer.

The previous frontier had:

* `numeratorBound`;
* `h_numeratorBound_nonneg`;
* `h_countWeightBound_le_numerator`;
* `h_numerator_div_denominator_tendsto_zero`.

That was too indirect.

This file sets the numerator to the actual product:

  `countBound n * weightBound n`.

So the remaining quotient obligation is now directly:

  `(countBound n * weightBound n) / denominatorBound s n → 0`.

This is a cleanup/reduction of the frontier, not another wrapper.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Sound-counting D-window data where the remaining count/weight quotient estimate
is supplied through separate factor bounds, with no artificial numerator layer.
-/
structure CanonicalPrimePowerDWindowSoundCountingFactorBoundsData
    (X : DFiniteStagePackageFromOperatorLayer) where

  /-- D-window data used to represent finite and shared kernels. -/
  W : DCanonicalWindowData

  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /-- Concrete cutoff growth: the prime-power cutoff dominates the stage index. -/
  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  /-- The finite stage index set contains every prime-power pair below cutoff. -/
  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /-- The finite stage index set contains only indices below cutoff. -/
  h_indices_subset_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        q.center ≤ (alpha n).R

  /-- Unweighted majorant for the D-window limit kernel. -/
  kernelMajorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the unweighted kernel majorant. -/
  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  /-- Structural identification of prime-power kernels with D-window kernels. -/
  kernelID :
    PrimePowerDWindowKernelIdentificationData X W alpha Kshared

  /-- Compact real coordinate set for each `s`. -/
  coordSet : ℂ → Set ℝ

  /-- Compactness of the coordinate set on the D overlap half-plane. -/
  h_coordSet_compact :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  /-- Active finite-stage prime-power coordinates lie in the coordinate set. -/
  h_coord_mem :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        kernelID.coord s q ∈ coordSet s

  /-- Pure D.CANONICAL-WINDOW compact inverse-speed theorem. -/
  windowSpeed :
    DCanonicalWindowCompactSpeedAPI W alpha

  /-- Majorant for the D-window limit kernel. -/
  h_windowLimit_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖W.G_limit (kernelID.coord s q)‖ ≤ kernelMajorant q

  /-- Summable comparison envelope for the weighted majorant. -/
  summabilityEnvelope : PrimePowerPair → ℝ

  /-- Weighted majorant is bounded by the summability envelope. -/
  h_weightedKernelMajorant_le_envelope :
    ∀ q : PrimePowerPair,
      ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q

  /-- The comparison envelope is summable. -/
  h_summabilityEnvelope_summable :
    Summable summabilityEnvelope

  /-- Sound cutoff/counting/real-weight mass data. -/
  soundMassCounting :
    PrimePowerSoundMassCountingSetWeightEnvelopeData

  /-- Explicit denominator lower bound for the compact D-window speed. -/
  denominatorBound : ℂ → ℕ → ℝ

  /-- Positivity of the denominator bound. -/
  h_denominatorBound_pos :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 < denominatorBound s n

  /-- Denominator bound is below the actual compact-window speed. -/
  h_denominatorBound_le_windowSpeed :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        denominatorBound s n ≤ windowSpeed.speed (coordSet s) n

  /--
  Separate bound for the counting envelope along the stage cutoff sequence.
  -/
  countBound : ℕ → ℝ

  /-- Nonnegativity of the count bound. -/
  h_countBound_nonneg :
    ∀ n : ℕ, 0 ≤ countBound n

  /--
  Count envelope along the cutoff is bounded by `countBound`.
  -/
  h_countEnvelope_le_countBound :
    ∀ n : ℕ,
      soundMassCounting.centerCountingSet.countEnvelope ((alpha n).R) ≤
        countBound n

  /--
  Separate bound for the real-weight envelope along the stage cutoff sequence.
  -/
  weightBound : ℕ → ℝ

  /-- Nonnegativity of the weight bound. -/
  h_weightBound_nonneg :
    ∀ n : ℕ, 0 ≤ weightBound n

  /--
  Weight envelope along the cutoff is bounded by `weightBound`.
  -/
  h_weightEnvelope_le_weightBound :
    ∀ n : ℕ,
      soundMassCounting.weightData.weightEnvelope ((alpha n).R) ≤
        weightBound n

  /--
  The actual count/weight numerator divided by the denominator tends to zero.

  This is now the real quotient target:
    `(countBound n * weightBound n) / denominatorBound s n → 0`.
  -/
  h_countBound_mul_weightBound_div_denominator_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (countBound n * weightBound n) / denominatorBound s n)
        Filter.atTop
        (𝓝 0)

/--
Convert factor-bound data into the previous sound-counting package by proving
the quotient-convergence field.

No artificial numerator is used: the numerator is exactly
`countBound n * weightBound n`.
-/
def CanonicalPrimePowerDWindowSoundCountingFactorBoundsData.toSoundCountingData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSoundCountingFactorBoundsData X) :
    CanonicalPrimePowerDWindowSoundCountingData X :=
  { W := S.W
    alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg

    kernelID := S.kernelID
    coordSet := S.coordSet
    h_coordSet_compact := S.h_coordSet_compact
    h_coord_mem := S.h_coord_mem

    windowSpeed := S.windowSpeed

    h_windowLimit_norm_le_majorant := S.h_windowLimit_norm_le_majorant

    summabilityEnvelope := S.summabilityEnvelope
    h_weightedKernelMajorant_le_envelope :=
      S.h_weightedKernelMajorant_le_envelope
    h_summabilityEnvelope_summable :=
      S.h_summabilityEnvelope_summable

    soundMassCounting := S.soundMassCounting

    denominatorBound := S.denominatorBound
    h_denominatorBound_pos := S.h_denominatorBound_pos
    h_denominatorBound_le_windowSpeed :=
      S.h_denominatorBound_le_windowSpeed

    h_countWeight_div_denominator_tendsto_zero := by
      intro s hs
      exact
        countWeight_div_denominator_tendsto_zero_of_cutoff_factor_bounds
          (fun n : ℕ => (S.alpha n).R)
          S.soundMassCounting.centerCountingSet.countEnvelope
          S.soundMassCounting.weightData.weightEnvelope
          S.countBound
          S.weightBound
          (S.denominatorBound s)
          (fun n : ℕ => S.countBound n * S.weightBound n)
          S.soundMassCounting.centerCountingSet.h_countEnvelope_nonneg
          S.soundMassCounting.weightData.h_weightEnvelope_nonneg
          S.h_countBound_nonneg
          (S.h_denominatorBound_pos s hs)
          (fun n : ℕ =>
            mul_nonneg
              (S.h_countBound_nonneg n)
              (S.h_weightBound_nonneg n))
          S.h_countEnvelope_le_countBound
          S.h_weightEnvelope_le_weightBound
          (fun n : ℕ => le_rfl)
          (S.h_countBound_mul_weightBound_div_denominator_tendsto_zero s hs) }

/--
Build `CanonicalPrimePowerExhaustionData` from factor-bound sound-counting data.
-/
def CanonicalPrimePowerDWindowSoundCountingFactorBoundsData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSoundCountingFactorBoundsData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toSoundCountingData.toExhaustionData

/--
Build `DBcanLimitData` directly from factor-bound sound-counting data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowSoundCountingFactorBounds
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSoundCountingFactorBoundsData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowSoundCounting
    X
    S.toSoundCountingData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once factor-bound sound-counting data is supplied.
-/
theorem canonicalPrimePowerDWindowSoundCountingFactorBounds_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSoundCountingFactorBoundsData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowSoundCountingFactorBounds X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowSoundCounting_h_Bcan_matches_tsum
      X
      S.toSoundCountingData
      s
      hs

end

end RHFormalization
