import RHFormalization.CanonicalPrimePowerWeightEnvelope

/-!
# RHFormalization.CanonicalPrimePowerCountingSetEnvelope

Counting-set envelope for prime-power cutoff mass.

This file is not an RH endpoint.

The current mass-counting frontier still carries

  h_card_le_countEnvelope :
    ((belowCutoff R).card : ℝ) ≤ countEnvelope R.

This file reduces that to a more concrete finite-combinatorial estimate:

* `belowCutoff R ⊆ countSet R`;
* `((countSet R).card : ℝ) ≤ countEnvelope R`.

This is the next real mass-side cut: the remaining task becomes constructing
and bounding an explicit finite counting set for prime-power pairs below cutoff.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A finite counting set enclosing the prime-power cutoff enumeration.
-/
structure PrimePowerCutoffCountingSetData
    (massEnum : PrimePowerWeightCutoffEnumerationData) where

  /--
  A finite set that contains all enumerated prime-power pairs below cutoff `R`.
  -/
  countSet : ℝ → Finset PrimePowerPair

  /--
  Real-valued envelope for the cardinality of the counting set.
  -/
  countEnvelope : ℝ → ℝ

  /--
  Nonnegativity of the count envelope.
  -/
  h_countEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ countEnvelope R

  /--
  The actual cutoff enumeration is contained in the counting set.
  -/
  h_belowCutoff_subset_countSet :
    ∀ R : ℝ,
      massEnum.belowCutoff R ⊆ countSet R

  /--
  Cardinality of the counting set is bounded by the count envelope.
  -/
  h_countSet_card_le_countEnvelope :
    ∀ R : ℝ,
      ((countSet R).card : ℝ) ≤ countEnvelope R

/--
The actual cutoff enumeration cardinality is bounded by the count envelope.
-/
theorem PrimePowerCutoffCountingSetData.card_belowCutoff_le_countEnvelope
    {massEnum : PrimePowerWeightCutoffEnumerationData}
    (C : PrimePowerCutoffCountingSetData massEnum) :
    ∀ R : ℝ,
      ((massEnum.belowCutoff R).card : ℝ) ≤ C.countEnvelope R := by
  intro R

  have hcardNat :
      (massEnum.belowCutoff R).card ≤ (C.countSet R).card :=
    Finset.card_le_card
      (C.h_belowCutoff_subset_countSet R)

  have hcardReal :
      ((massEnum.belowCutoff R).card : ℝ) ≤
        ((C.countSet R).card : ℝ) := by
    exact_mod_cast hcardNat

  exact le_trans hcardReal (C.h_countSet_card_le_countEnvelope R)

/--
Mass-counting data where the count envelope is obtained from an explicit
finite counting set, while the weight estimate remains the real-weight envelope.
-/
structure PrimePowerMassCountingSetWeightEnvelopeData
    (massEnum : PrimePowerWeightCutoffEnumerationData) where

  /--
  Explicit finite counting-set data.
  -/
  countingSetData :
    PrimePowerCutoffCountingSetData massEnum

  /--
  Concrete real-weight envelope data.
  -/
  weightData :
    PrimePowerWeightEnvelopeData massEnum

/--
Convert counting-set/real-weight data into the previous mass-counting
weight-envelope data.
-/
def PrimePowerMassCountingSetWeightEnvelopeData.toMassCountingWeightEnvelopeData
    {massEnum : PrimePowerWeightCutoffEnumerationData}
    (M : PrimePowerMassCountingSetWeightEnvelopeData massEnum) :
    PrimePowerMassCountingWeightEnvelopeData massEnum :=
  { countEnvelope := M.countingSetData.countEnvelope

    h_countEnvelope_nonneg :=
      M.countingSetData.h_countEnvelope_nonneg

    h_card_le_countEnvelope :=
      M.countingSetData.card_belowCutoff_le_countEnvelope

    weightData := M.weightData }

/--
D-window mass-counting data where the finite count estimate is supplied through
an explicit counting set.
-/
structure CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData
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
  Concrete counting-set/real-weight envelope for exact enumerated mass.
  -/
  massCountingSetWeightEnvelope :
    PrimePowerMassCountingSetWeightEnvelopeData massEnum

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
  The concrete counting-set/weight quotient tends to zero.
  -/
  h_countWeight_div_denominator_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (massCountingSetWeightEnvelope.countingSetData.countEnvelope ((alpha n).R) *
            massCountingSetWeightEnvelope.weightData.weightEnvelope ((alpha n).R)) /
            denominatorBound s n)
        Filter.atTop
        (𝓝 0)

/--
Convert counting-set/real-weight D-window data into the previous
mass-counting/real-weight data.
-/
def CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData.toMassCountingWeightEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData X) :
    CanonicalPrimePowerDWindowMassCountingWeightEnvelopeData X :=
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

    massCountingWeightEnvelope :=
      S.massCountingSetWeightEnvelope.toMassCountingWeightEnvelopeData

    denominatorBound := S.denominatorBound
    h_denominatorBound_pos := S.h_denominatorBound_pos
    h_denominatorBound_le_windowSpeed :=
      S.h_denominatorBound_le_windowSpeed

    h_countWeight_div_denominator_tendsto_zero :=
      S.h_countWeight_div_denominator_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from counting-set/real-weight data.
-/
def CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassCountingWeightEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` directly from counting-set/real-weight data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCountingSetWeightEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCountingWeightEnvelope
    X
    S.toMassCountingWeightEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once counting-set/real-weight data is supplied.
-/
theorem canonicalPrimePowerDWindowMassCountingSetWeightEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCountingSetWeightEnvelope X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowMassCountingWeightEnvelope_h_Bcan_matches_tsum
      X
      S.toMassCountingWeightEnvelopeData
      s
      hs

end

end RHFormalization
