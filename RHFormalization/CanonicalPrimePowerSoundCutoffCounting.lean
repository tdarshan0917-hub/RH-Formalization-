import RHFormalization.CanonicalPrimePowerCountingSetEnvelope

/-!
# RHFormalization.CanonicalPrimePowerSoundCutoffCounting

Sound cutoff enumeration for prime-power counting.

This file is not an RH endpoint.

The previous counting-set layer reduced the cardinality estimate to

  belowCutoff R ⊆ countSet R.

But `PrimePowerWeightCutoffEnumerationData` only records completeness:

  q.center ≤ R → q ∈ belowCutoff R.

For counting estimates we also need soundness:

  q ∈ belowCutoff R → q.center ≤ R.

This file introduces that soundness field and uses it to derive
`belowCutoff R ⊆ countSet R` from the simpler counting-set condition

  q.center ≤ R → q ∈ countSet R.

This is a real finite-combinatorial mass-side cut.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A sound finite cutoff enumeration.

The existing `PrimePowerWeightCutoffEnumerationData` gives completeness:
all prime powers below cutoff are included.  This adds the reverse direction:
everything included is actually below cutoff.
-/
structure PrimePowerSoundCutoffEnumerationData where

  /-- The underlying finite cutoff enumeration. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /--
  Soundness of the finite cutoff enumeration.
  -/
  h_belowCutoff_center_le :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q ∈ massEnum.belowCutoff R →
        q.center ≤ R

/--
If a counting set contains every prime-power pair with `q.center ≤ R`, then it
contains the sound `belowCutoff R` enumeration.
-/
theorem belowCutoff_subset_countSet_of_sound_center_cutoff
    (E : PrimePowerSoundCutoffEnumerationData)
    (countSet : ℝ → Finset PrimePowerPair)
    (h_center_le_mem_countSet :
      ∀ R : ℝ,
      ∀ q : PrimePowerPair,
        q.center ≤ R →
          q ∈ countSet R) :
    ∀ R : ℝ,
      E.massEnum.belowCutoff R ⊆ countSet R := by
  intro R q hq
  exact
    h_center_le_mem_countSet
      R
      q
      (E.h_belowCutoff_center_le R q hq)

/--
Counting-set data built from a sound cutoff enumeration and a center-based
counting set.
-/
structure PrimePowerCenterCountingSetData
    (E : PrimePowerSoundCutoffEnumerationData) where

  /--
  Explicit finite counting set.
  -/
  countSet : ℝ → Finset PrimePowerPair

  /--
  Real-valued cardinality envelope.
  -/
  countEnvelope : ℝ → ℝ

  /--
  Nonnegativity of the count envelope.
  -/
  h_countEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ countEnvelope R

  /--
  Every prime-power pair with center below cutoff lies in the counting set.
  -/
  h_center_le_mem_countSet :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q.center ≤ R →
        q ∈ countSet R

  /--
  Cardinality of the counting set is bounded by the count envelope.
  -/
  h_countSet_card_le_countEnvelope :
    ∀ R : ℝ,
      ((countSet R).card : ℝ) ≤ countEnvelope R

/--
Convert center-based counting set data into the previous cutoff counting-set
data.
-/
def PrimePowerCenterCountingSetData.toCutoffCountingSetData
    {E : PrimePowerSoundCutoffEnumerationData}
    (C : PrimePowerCenterCountingSetData E) :
    PrimePowerCutoffCountingSetData E.massEnum :=
  { countSet := C.countSet
    countEnvelope := C.countEnvelope

    h_countEnvelope_nonneg :=
      C.h_countEnvelope_nonneg

    h_belowCutoff_subset_countSet :=
      belowCutoff_subset_countSet_of_sound_center_cutoff
        E
        C.countSet
        C.h_center_le_mem_countSet

    h_countSet_card_le_countEnvelope :=
      C.h_countSet_card_le_countEnvelope }

/--
Mass-counting data using a sound cutoff enumeration and center-based counting
set, while keeping the real-weight envelope.
-/
structure PrimePowerSoundMassCountingSetWeightEnvelopeData where

  /-- Sound finite cutoff enumeration. -/
  soundEnum : PrimePowerSoundCutoffEnumerationData

  /-- Center-based finite counting set. -/
  centerCountingSet :
    PrimePowerCenterCountingSetData soundEnum

  /-- Real-weight envelope data. -/
  weightData :
    PrimePowerWeightEnvelopeData soundEnum.massEnum

/--
Convert sound center-counting data into the previous counting-set/real-weight
envelope data.
-/
def PrimePowerSoundMassCountingSetWeightEnvelopeData.toMassCountingSetWeightEnvelopeData
    (M : PrimePowerSoundMassCountingSetWeightEnvelopeData) :
    PrimePowerMassCountingSetWeightEnvelopeData M.soundEnum.massEnum :=
  { countingSetData :=
      M.centerCountingSet.toCutoffCountingSetData

    weightData :=
      M.weightData }

/--
D-window package using a sound cutoff enumeration and center-based counting set.

Compared with `CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData`,
this replaces the raw `massEnum` plus counting-set data by a sound cutoff
enumeration and center-based count-set condition.
-/
structure CanonicalPrimePowerDWindowSoundCountingData
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

  /--
  Sound cutoff/counting/real-weight mass data.
  -/
  soundMassCounting :
    PrimePowerSoundMassCountingSetWeightEnvelopeData

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
  The concrete count/weight quotient tends to zero.
  -/
  h_countWeight_div_denominator_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (soundMassCounting.centerCountingSet.countEnvelope ((alpha n).R) *
            soundMassCounting.weightData.weightEnvelope ((alpha n).R)) /
            denominatorBound s n)
        Filter.atTop
        (𝓝 0)

/--
Convert sound cutoff/counting data into the previous counting-set/real-weight
D-window package.
-/
def CanonicalPrimePowerDWindowSoundCountingData.toMassCountingSetWeightEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSoundCountingData X) :
    CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData X :=
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

    massEnum := S.soundMassCounting.soundEnum.massEnum

    massCountingSetWeightEnvelope :=
      S.soundMassCounting.toMassCountingSetWeightEnvelopeData

    denominatorBound := S.denominatorBound
    h_denominatorBound_pos := S.h_denominatorBound_pos
    h_denominatorBound_le_windowSpeed :=
      S.h_denominatorBound_le_windowSpeed

    h_countWeight_div_denominator_tendsto_zero :=
      S.h_countWeight_div_denominator_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from sound counting data.
-/
def CanonicalPrimePowerDWindowSoundCountingData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSoundCountingData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassCountingSetWeightEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` directly from sound counting data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowSoundCounting
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSoundCountingData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassCountingSetWeightEnvelope
    X
    S.toMassCountingSetWeightEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once sound counting data is supplied.
-/
theorem canonicalPrimePowerDWindowSoundCounting_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSoundCountingData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowSoundCounting X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowMassCountingSetWeightEnvelope_h_Bcan_matches_tsum
      X
      S.toMassCountingSetWeightEnvelopeData
      s
      hs

end

end RHFormalization
