import RHFormalization.CanonicalPrimePowerMassCountingEnvelope

/-!
# RHFormalization.CanonicalPrimePowerWeightEnvelope

Concrete weight-envelope layer for prime-power mass counting.

This file is not an RH endpoint.

The current mass-counting frontier contains the field

  h_weight_le_weightEnvelope :
    ∀ R q, q ∈ belowCutoff R → ‖q.weightC‖ ≤ weightEnvelope R.

This file reduces that field to a real-valued absolute-value estimate on the
frozen normalized prime-power weight.

This is the next surgical mass-side cut: it directly uses the project's
`q.weightC = (q.weightReal : ℂ)` normalization.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The complex norm of the canonical prime-power weight is the real norm of the
stored real weight.
-/
theorem PrimePowerPair.norm_weightC_eq_abs_weightReal
    (q : PrimePowerPair) :
    ‖q.weightC‖ = |q.weightReal| := by
  simp [PrimePowerPair.weightC]

/--
A real absolute-value bound for `q.weightReal` implies the corresponding complex
weight bound for `q.weightC`.
-/
theorem PrimePowerPair.norm_weightC_le_of_abs_weightReal_le
    (q : PrimePowerPair)
    {B : ℝ}
    (hB : |q.weightReal| ≤ B) :
    ‖q.weightC‖ ≤ B := by
  simpa [PrimePowerPair.norm_weightC_eq_abs_weightReal q] using hB

/--
Concrete weight-envelope data for a finite prime-power cutoff enumeration.

This packages the actual remaining weight estimate:
`|q.weightReal| ≤ weightEnvelope R` on the enumerated cutoff set.
-/
structure PrimePowerWeightEnvelopeData
    (massEnum : PrimePowerWeightCutoffEnumerationData) where

  /-- Upper envelope for the normalized prime-power weight size below cutoff. -/
  weightEnvelope : ℝ → ℝ

  /-- Nonnegativity of the weight envelope. -/
  h_weightEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ weightEnvelope R

  /--
  Real-valued bound for the frozen normalized prime-power weight.
  -/
  h_abs_weightReal_le :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q ∈ massEnum.belowCutoff R →
        |q.weightReal| ≤ weightEnvelope R

/--
Extract the complex-weight bound required by the mass-counting layer.
-/
theorem PrimePowerWeightEnvelopeData.norm_weightC_le
    {massEnum : PrimePowerWeightCutoffEnumerationData}
    (W : PrimePowerWeightEnvelopeData massEnum) :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q ∈ massEnum.belowCutoff R →
        ‖q.weightC‖ ≤ W.weightEnvelope R := by
  intro R q hq
  exact
    PrimePowerPair.norm_weightC_le_of_abs_weightReal_le
      q
      (W.h_abs_weightReal_le R q hq)

/--
Mass-counting data where the weight envelope is supplied through the actual
`weightReal` normalization.

Compared with `PrimePowerMassCountingEnvelopeData`, this replaces the raw field

  h_weight_le_weightEnvelope :
    ‖q.weightC‖ ≤ weightEnvelope R

by the sharper real-weight field

  |q.weightReal| ≤ weightEnvelope R.
-/
structure PrimePowerMassCountingWeightEnvelopeData
    (massEnum : PrimePowerWeightCutoffEnumerationData) where

  /-- Upper envelope for the number of prime-power pairs below cutoff. -/
  countEnvelope : ℝ → ℝ

  /-- Nonnegativity of the count envelope. -/
  h_countEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ countEnvelope R

  /-- Finite enumeration cardinality is bounded by the count envelope. -/
  h_card_le_countEnvelope :
    ∀ R : ℝ,
      ((massEnum.belowCutoff R).card : ℝ) ≤ countEnvelope R

  /-- Concrete real-weight envelope data. -/
  weightData : PrimePowerWeightEnvelopeData massEnum

/--
Convert real-weight-envelope mass counting data into the previous
counting/weight envelope data.
-/
def PrimePowerMassCountingWeightEnvelopeData.toMassCountingEnvelopeData
    {massEnum : PrimePowerWeightCutoffEnumerationData}
    (M : PrimePowerMassCountingWeightEnvelopeData massEnum) :
    PrimePowerMassCountingEnvelopeData massEnum :=
  { countEnvelope := M.countEnvelope
    weightEnvelope := M.weightData.weightEnvelope

    h_countEnvelope_nonneg := M.h_countEnvelope_nonneg
    h_weightEnvelope_nonneg := M.weightData.h_weightEnvelope_nonneg

    h_card_le_countEnvelope := M.h_card_le_countEnvelope

    h_weight_le_weightEnvelope := by
      intro R q hq
      exact M.weightData.norm_weightC_le R q hq }

/--
D-window mass-counting data where the weight estimate is stated using
`weightReal`.

Compared with `CanonicalPrimePowerDWindowMassCountingSpeedComparisonData`, this
replaces `massCountingEnvelope` by `massCountingWeightEnvelope`.
-/
structure CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData
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
      IsPrimePowerPair q →
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
  Concrete counting/real-weight envelope for exact enumerated mass.
  -/
  massCountingWeightEnvelope :
    PrimePowerMassCountingWeightEnvelopeData massEnum

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
          (massCountingWeightEnvelope.countEnvelope ((alpha n).R) *
            massCountingWeightEnvelope.weightData.weightEnvelope ((alpha n).R)) /
            denominatorBound s n)
        Filter.atTop
        (𝓝 0)

/--
Convert real-weight-envelope D-window data into the previous mass-counting data.
-/
def CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData.toMassCountingSpeedComparisonData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData X) :
    CanonicalPrimePowerDWindowMassCountingSpeedComparisonData X :=
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
    massCountingEnvelope :=
      S.massCountingWeightEnvelope.toMassCountingEnvelopeData

    denominatorBound := S.denominatorBound
    h_denominatorBound_pos := S.h_denominatorBound_pos
    h_denominatorBound_le_windowSpeed :=
      S.h_denominatorBound_le_windowSpeed

    h_countWeight_div_denominator_tendsto_zero :=
      S.h_countWeight_div_denominator_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from real-weight-envelope data.
-/
def CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassCountingSpeedComparisonData.toExhaustionData

/--
Build `DBcanLimitData` directly from real-weight-envelope data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCountingWeightEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCounting
    X
    S.toMassCountingSpeedComparisonData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once real-weight-envelope data is supplied.
-/
theorem canonicalPrimePowerDWindowMassCountingWeightEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCountingWeightEnvelope X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowMassCounting_h_Bcan_matches_tsum
      X
      S.toMassCountingSpeedComparisonData
      s
      hs

end

end RHFormalization
