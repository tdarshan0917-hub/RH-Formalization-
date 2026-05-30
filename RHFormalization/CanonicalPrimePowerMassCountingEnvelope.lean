import RHFormalization.CanonicalPrimePowerMassEnvelopeSpeedComparison

/-!
# RHFormalization.CanonicalPrimePowerMassCountingEnvelope

Counting/weight envelope for the exact prime-power mass.

This file is not an RH endpoint.

The current frontier still carries an abstract mass envelope

  enumeratedPrimePowerMass massEnum R ≤ massEnvelope R

and then a further numerator bound. This file makes the mass envelope concrete:

  massEnvelope R := countEnvelope R * weightEnvelope R.

The mass estimate follows from:
* card(belowCutoff R) ≤ countEnvelope R;
* every active weight norm is ≤ weightEnvelope R.

This is a real mass-side estimate cut.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Exact enumerated mass is bounded by finite cardinality times a uniform weight
bound on the cutoff set.
-/
theorem enumeratedPrimePowerMass_le_card_mul_weightBound
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (weightBound : ℝ)
    (h_weight_le :
      ∀ q : PrimePowerPair,
        q ∈ massEnum.belowCutoff R →
          ‖q.weightC‖ ≤ weightBound) :
    enumeratedPrimePowerMass massEnum R ≤
      ((massEnum.belowCutoff R).card : ℝ) * weightBound := by
  have hsum :
      (massEnum.belowCutoff R).sum
          (fun q : PrimePowerPair => ‖q.weightC‖) ≤
        (massEnum.belowCutoff R).sum
          (fun _q : PrimePowerPair => weightBound) := by
    exact
      Finset.sum_le_sum
        (fun q hq => h_weight_le q hq)

  simpa [enumeratedPrimePowerMass, Finset.sum_const, nsmul_eq_mul]
    using hsum

/--
Exact enumerated mass is bounded by a count envelope times a weight envelope.
-/
theorem enumeratedPrimePowerMass_le_countEnvelope_mul_weightEnvelope
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (countEnvelope weightEnvelope : ℝ)
    (h_card_le_countEnvelope :
      ((massEnum.belowCutoff R).card : ℝ) ≤ countEnvelope)
    (h_weightEnvelope_nonneg :
      0 ≤ weightEnvelope)
    (h_weight_le_weightEnvelope :
      ∀ q : PrimePowerPair,
        q ∈ massEnum.belowCutoff R →
          ‖q.weightC‖ ≤ weightEnvelope) :
    enumeratedPrimePowerMass massEnum R ≤
      countEnvelope * weightEnvelope := by
  have hmass_card :
      enumeratedPrimePowerMass massEnum R ≤
        ((massEnum.belowCutoff R).card : ℝ) * weightEnvelope :=
    enumeratedPrimePowerMass_le_card_mul_weightBound
      massEnum
      R
      weightEnvelope
      h_weight_le_weightEnvelope

  have hcard :
      ((massEnum.belowCutoff R).card : ℝ) * weightEnvelope ≤
        countEnvelope * weightEnvelope :=
    mul_le_mul_of_nonneg_right
      h_card_le_countEnvelope
      h_weightEnvelope_nonneg

  exact le_trans hmass_card hcard

/--
Concrete counting/weight envelope for the exact enumerated prime-power mass.
-/
structure PrimePowerMassCountingEnvelopeData
    (massEnum : PrimePowerWeightCutoffEnumerationData) where

  /-- Upper envelope for the number of prime-power pairs below cutoff. -/
  countEnvelope : ℝ → ℝ

  /-- Upper envelope for the normalized weight size below cutoff. -/
  weightEnvelope : ℝ → ℝ

  /-- Nonnegativity of the count envelope. -/
  h_countEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ countEnvelope R

  /-- Nonnegativity of the weight envelope. -/
  h_weightEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ weightEnvelope R

  /-- Finite enumeration cardinality is bounded by the count envelope. -/
  h_card_le_countEnvelope :
    ∀ R : ℝ,
      ((massEnum.belowCutoff R).card : ℝ) ≤ countEnvelope R

  /-- Each enumerated weight is bounded by the weight envelope. -/
  h_weight_le_weightEnvelope :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q ∈ massEnum.belowCutoff R →
        ‖q.weightC‖ ≤ weightEnvelope R

/--
Convert counting/weight envelope data into `PrimePowerMassEnvelopeData`.
-/
def PrimePowerMassCountingEnvelopeData.toMassEnvelopeData
    {massEnum : PrimePowerWeightCutoffEnumerationData}
    (M : PrimePowerMassCountingEnvelopeData massEnum) :
    PrimePowerMassEnvelopeData massEnum :=
  { massEnvelope := fun R : ℝ =>
      M.countEnvelope R * M.weightEnvelope R

    h_massEnvelope_nonneg := by
      intro R
      exact
        mul_nonneg
          (M.h_countEnvelope_nonneg R)
          (M.h_weightEnvelope_nonneg R)

    h_exactMass_le_envelope := by
      intro R
      exact
        enumeratedPrimePowerMass_le_countEnvelope_mul_weightEnvelope
          massEnum
          R
          (M.countEnvelope R)
          (M.weightEnvelope R)
          (M.h_card_le_countEnvelope R)
          (M.h_weightEnvelope_nonneg R)
          (M.h_weight_le_weightEnvelope R) }

/--
D-window mass-envelope/speed-comparison data using a concrete counting/weight
mass envelope.

Compared with `CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData`, this
removes:
* `massEnvelopeData`;
* `numeratorBound`;
* `h_massEnvelope_le_numeratorBound`.

The numerator is exactly:

  countEnvelope(R_n) * weightEnvelope(R_n).
-/
structure CanonicalPrimePowerDWindowMassCountingSpeedComparisonData
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
  Concrete counting/weight envelope for exact enumerated mass.
  -/
  massCountingEnvelope :
    PrimePowerMassCountingEnvelopeData massEnum

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
  The concrete counting/weight quotient tends to zero.
  -/
  h_countWeight_div_denominator_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (massCountingEnvelope.countEnvelope ((alpha n).R) *
            massCountingEnvelope.weightEnvelope ((alpha n).R)) /
            denominatorBound s n)
        Filter.atTop
        (𝓝 0)

/--
Convert counting/weight mass data into the previous mass-envelope/speed-
comparison package.
-/
def CanonicalPrimePowerDWindowMassCountingSpeedComparisonData.toMassEnvelopeSpeedComparisonData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassCountingSpeedComparisonData X) :
    CanonicalPrimePowerDWindowMassEnvelopeSpeedComparisonData X :=
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

    h_windowLimit_norm_le_majorant :=
      S.h_windowLimit_norm_le_majorant

    summabilityEnvelope := S.summabilityEnvelope
    h_weightedKernelMajorant_le_envelope :=
      S.h_weightedKernelMajorant_le_envelope
    h_summabilityEnvelope_summable :=
      S.h_summabilityEnvelope_summable

    massEnum := S.massEnum
    massEnvelopeData := S.massCountingEnvelope.toMassEnvelopeData

    numeratorBound := fun _s n =>
      S.massCountingEnvelope.countEnvelope ((S.alpha n).R) *
        S.massCountingEnvelope.weightEnvelope ((S.alpha n).R)

    h_numeratorBound_nonneg := by
      intro s hs n
      exact
        mul_nonneg
          (S.massCountingEnvelope.h_countEnvelope_nonneg ((S.alpha n).R))
          (S.massCountingEnvelope.h_weightEnvelope_nonneg ((S.alpha n).R))

    h_massEnvelope_le_numeratorBound := by
      intro s hs n
      exact le_rfl

    denominatorBound := S.denominatorBound
    h_denominatorBound_pos := S.h_denominatorBound_pos
    h_denominatorBound_le_windowSpeed :=
      S.h_denominatorBound_le_windowSpeed

    h_numerator_div_denominator_tendsto_zero :=
      S.h_countWeight_div_denominator_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from counting/weight mass data.
-/
def CanonicalPrimePowerDWindowMassCountingSpeedComparisonData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassCountingSpeedComparisonData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassEnvelopeSpeedComparisonData.toExhaustionData

/--
Build `DBcanLimitData` directly from counting/weight mass data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCounting
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassCountingSpeedComparisonData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelopeSpeedComparison
    X
    S.toMassEnvelopeSpeedComparisonData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once counting/weight mass data is supplied.
-/
theorem canonicalPrimePowerDWindowMassCounting_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassCountingSpeedComparisonData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCounting X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowMassEnvelopeSpeedComparison_h_Bcan_matches_tsum
      X
      S.toMassEnvelopeSpeedComparisonData
      s
      hs

end

end RHFormalization
