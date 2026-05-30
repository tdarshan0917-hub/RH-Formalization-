import RHFormalization.CanonicalPrimePowerMassUpperEnvelope

/-!
# RHFormalization.CanonicalPrimePowerMassEnvelopeSpeedComparison

Comparison layer for the remaining mass-envelope / D-window-speed asymptotic.

This file is not an RH endpoint.

The current sharp frontier contains the analytic field

  massEnvelope(R_n) / windowSpeed(coordSet s,n) → 0.

This file reduces that field to a concrete upper/lower comparison:

* massEnvelope(R_n) ≤ numeratorBound(s,n);
* denominatorBound(s,n) ≤ windowSpeed(coordSet s,n);
* numeratorBound(s,n) / denominatorBound(s,n) → 0.

This is a direct attack on the remaining mass/window speed estimate.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If a mass envelope is bounded above by `numeratorBound`, and the D-window speed
is bounded below by `denominatorBound`, then the desired mass/speed quotient
tends to zero once `numeratorBound / denominatorBound → 0`.
-/
theorem massEnvelope_div_windowSpeed_tendsto_zero_of_comparison
    (massEnvelope windowSpeed numeratorBound denominatorBound : ℕ → ℝ)
    (h_massEnvelope_nonneg :
      ∀ n : ℕ, 0 ≤ massEnvelope n)
    (h_numeratorBound_nonneg :
      ∀ n : ℕ, 0 ≤ numeratorBound n)
    (h_windowSpeed_pos :
      ∀ n : ℕ, 0 < windowSpeed n)
    (h_denominatorBound_pos :
      ∀ n : ℕ, 0 < denominatorBound n)
    (h_massEnvelope_le_numeratorBound :
      ∀ n : ℕ, massEnvelope n ≤ numeratorBound n)
    (h_denominatorBound_le_windowSpeed :
      ∀ n : ℕ, denominatorBound n ≤ windowSpeed n)
    (h_numerator_div_denominator_tendsto_zero :
      Tendsto
        (fun n : ℕ => numeratorBound n / denominatorBound n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ => massEnvelope n / windowSpeed n)
      Filter.atTop
      (𝓝 0) := by
  exact
    exactMass_div_speed_tendsto_zero_of_upper_lower
      massEnvelope
      numeratorBound
      windowSpeed
      denominatorBound
      h_massEnvelope_nonneg
      h_numeratorBound_nonneg
      h_windowSpeed_pos
      h_denominatorBound_pos
      h_massEnvelope_le_numeratorBound
      h_denominatorBound_le_windowSpeed
      h_numerator_div_denominator_tendsto_zero

/--
Mass-envelope data where the mass/window-speed asymptotic is proved by an
explicit comparison pair.

Compared with `CanonicalPrimePowerDWindowMassEnvelopeData`, this removes

  h_massEnvelope_div_windowSpeed_tendsto_zero

and replaces it with:
* a numerator bound for the mass envelope;
* a denominator lower bound for the compact-window speed;
* convergence of numerator/denominator to zero.
-/
structure CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData
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

  /--
  Structural identification of prime-power kernels with D-window kernels.
  -/
  kernelID :
    PrimePowerDWindowKernelIdentificationData X W alpha Kshared

  /--
  Compact real coordinate set for each `s`.
  -/
  coordSet : ℂ → Set ℝ

  /--
  Compactness of the coordinate set on the D overlap half-plane.
  -/
  h_coordSet_compact :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  /--
  Active finite-stage prime-power coordinates lie in the coordinate set.
  -/
  h_coord_mem :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        kernelID.coord s q ∈ coordSet s

  /--
  Pure D.CANONICAL-WINDOW compact inverse-speed theorem.
  -/
  windowSpeed :
    DCanonicalWindowCompactSpeedAPI W alpha

  /--
  Majorant for the D-window limit kernel.
  -/
  h_windowLimit_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖W.G_limit (kernelID.coord s q)‖ ≤ kernelMajorant q

  /--
  Summable comparison envelope for the weighted majorant.
  -/
  summabilityEnvelope : PrimePowerPair → ℝ

  /--
  Weighted majorant is bounded by the summability envelope.
  -/
  h_weightedKernelMajorant_le_envelope :
    ∀ q : PrimePowerPair,
      ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q

  /--
  The comparison envelope is summable.
  -/
  h_summabilityEnvelope_summable :
    Summable summabilityEnvelope

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /--
  Cutoff mass envelope controlling the exact enumerated prime-power mass.
  -/
  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  /--
  Explicit numerator upper bound for the mass envelope along the stage sequence.
  -/
  numeratorBound : ℂ → ℕ → ℝ

  /-- Nonnegativity of the numerator bound. -/
  h_numeratorBound_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ numeratorBound s n

  /--
  Mass envelope along the stage sequence is bounded by the numerator bound.
  -/
  h_massEnvelope_le_numeratorBound :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        massEnvelopeData.massEnvelope ((alpha n).R) ≤ numeratorBound s n

  /--
  Explicit denominator lower bound for the compact D-window speed.
  -/
  denominatorBound : ℂ → ℕ → ℝ

  /-- Positivity of the denominator bound. -/
  h_denominatorBound_pos :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 < denominatorBound s n

  /--
  Denominator bound is below the actual compact-window speed.
  -/
  h_denominatorBound_le_windowSpeed :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        denominatorBound s n ≤ windowSpeed.speed (coordSet s) n

  /--
  The comparison quotient tends to zero.
  -/
  h_numerator_div_denominator_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => numeratorBound s n / denominatorBound s n)
        Filter.atTop
        (𝓝 0)

/--
Convert comparison data into the previous mass-envelope package.
-/
def CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData.toMassEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData X) :
    CanonicalPrimePowerDWindowMassEnvelopeData X :=
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

    massEnum := S.massEnum
    massEnvelopeData := S.massEnvelopeData

    h_massEnvelope_div_windowSpeed_tendsto_zero := by
      intro s hs
      exact
        massEnvelope_div_windowSpeed_tendsto_zero_of_comparison
          (fun n : ℕ => S.massEnvelopeData.massEnvelope ((S.alpha n).R))
          (fun n : ℕ => S.windowSpeed.speed (S.coordSet s) n)
          (S.numeratorBound s)
          (S.denominatorBound s)
          (fun n : ℕ =>
            S.massEnvelopeData.h_massEnvelope_nonneg ((S.alpha n).R))
          (S.h_numeratorBound_nonneg s hs)
          (fun n : ℕ =>
            S.windowSpeed.h_speed_pos
              (S.coordSet s)
              (S.h_coordSet_compact s hs)
              n)
          (S.h_denominatorBound_pos s hs)
          (S.h_massEnvelope_le_numeratorBound s hs)
          (S.h_denominatorBound_le_windowSpeed s hs)
          (S.h_numerator_div_denominator_tendsto_zero s hs) }

/--
Build `CanonicalPrimePowerExhaustionData` from comparison data.
-/
def CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` directly from comparison data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelopeSpeedComparison
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelope
    X
    S.toMassEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once mass-envelope/speed-comparison data is supplied.
-/
theorem canonicalPrimePowerDWindowMassEnvelopeSpeedComparison_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelopeSpeedComparison X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowMassEnvelope_h_Bcan_matches_tsum
      X
      S.toMassEnvelopeData
      s
      hs

end

end RHFormalization
