import RHFormalization.CanonicalPrimePowerDWindowExactWindowSpeed

/-!
# RHFormalization.CanonicalPrimePowerWeightedSummabilityEnvelope

Weighted summability by comparison envelope.

This file is not an RH endpoint.

The current sharp D-side frontier still carries

  h_weightedKernelMajorant_summable :
    Summable (fun q => ‖q.weightC‖ * kernelMajorant q).

This file reduces that to a concrete comparison estimate:

  ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q,

together with summability of `summabilityEnvelope`.

This is a direct attack on one of the remaining analytic estimate fields.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Weighted kernel-majorant summability by comparison with a nonnegative summable
envelope.
-/
theorem weightedKernelMajorant_summable_of_envelope
    (kernelMajorant summabilityEnvelope : PrimePowerPair → ℝ)
    (h_kernelMajorant_nonneg :
      ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q)
    (h_weighted_le_envelope :
      ∀ q : PrimePowerPair,
        ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q)
    (h_summabilityEnvelope_summable :
      Summable summabilityEnvelope) :
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * kernelMajorant q) := by
  exact
    Summable.of_nonneg_of_le
      (fun q : PrimePowerPair =>
        mul_nonneg
          (norm_nonneg q.weightC)
          (h_kernelMajorant_nonneg q))
      h_weighted_le_envelope
      h_summabilityEnvelope_summable

/--
Exact-window-speed D-side data where weighted summability is proved from a
summable comparison envelope.

Compared with `CanonicalPrimePowerDWindowExactWindowSpeedData`, this removes

  `h_weightedKernelMajorant_summable`

and replaces it by:

* `summabilityEnvelope`;
* a pointwise weighted-majorant bound by that envelope;
* summability of the envelope.
-/
structure CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData
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

  /-- Upper bound for exact enumerated prime-power mass. -/
  massUpper : ℕ → ℝ

  /-- Nonnegativity of the mass upper bound. -/
  h_massUpper_nonneg :
    ∀ n : ℕ, 0 ≤ massUpper n

  /-- Exact enumerated mass below `R_n` is bounded by `massUpper n`. -/
  h_exactMass_le_massUpper :
    ∀ n : ℕ,
      enumeratedPrimePowerMass massEnum ((alpha n).R) ≤
        massUpper n

  /--
  Mass upper bound divided by the actual compact D-window speed tends to zero.
  -/
  h_massUpper_div_windowSpeed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          massUpper n / windowSpeed.speed (coordSet s) n)
        Filter.atTop
        (𝓝 0)

/--
Convert envelope-summability data into the previous exact-window-speed data.
-/
def CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData.toExactWindowSpeedData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData X) :
    CanonicalPrimePowerDWindowExactWindowSpeedData X :=
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

    h_weightedKernelMajorant_summable :=
      weightedKernelMajorant_summable_of_envelope
        S.kernelMajorant
        S.summabilityEnvelope
        S.h_kernelMajorant_nonneg
        S.h_weightedKernelMajorant_le_envelope
        S.h_summabilityEnvelope_summable

    massEnum := S.massEnum
    massUpper := S.massUpper
    h_massUpper_nonneg := S.h_massUpper_nonneg
    h_exactMass_le_massUpper := S.h_exactMass_le_massUpper

    h_massUpper_div_windowSpeed_tendsto_zero :=
      S.h_massUpper_div_windowSpeed_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from exact-window-speed envelope data.
-/
def CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toExactWindowSpeedData.toExhaustionData

/--
Build `DBcanLimitData` directly from exact-window-speed envelope data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactWindowSpeedEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactWindowSpeed
    X
    S.toExactWindowSpeedData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once exact-window-speed envelope data is supplied.
-/
theorem canonicalPrimePowerDWindowExactWindowSpeedEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactWindowSpeedEnvelope X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowExactWindowSpeed_h_Bcan_matches_tsum
      X
      S.toExactWindowSpeedData
      s
      hs

end

end RHFormalization
