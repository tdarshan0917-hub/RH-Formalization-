import RHFormalization.CanonicalPrimePowerWeightedSummabilityEnvelope

/-!
# RHFormalization.CanonicalPrimePowerMassUpperEnvelope

Cutoff mass-envelope version of the D-window exact-speed frontier.

This file is not an RH endpoint.

The current frontier still carries an abstract stage-indexed mass bound

  massUpper : ℕ → ℝ

with

  exactMass(R_n) ≤ massUpper n,
  massUpper n / windowSpeed(coordSet s,n) → 0.

This file replaces that abstraction by a cutoff mass envelope

  massEnvelope : ℝ → ℝ,

so that

  massUpper n := massEnvelope ((alpha n).R).

The remaining mass-side analytic work becomes:
* prove exact enumerated prime-power mass below `R` is ≤ `massEnvelope R`;
* prove `massEnvelope R_n / windowSpeed(coordSet s,n) → 0`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A cutoff mass envelope for the exact enumerated prime-power mass.
-/
structure PrimePowerMassEnvelopeData
    (massEnum : PrimePowerWeightCutoffEnumerationData) where

  /--
  Envelope as a function of the real cutoff `R`.
  -/
  massEnvelope : ℝ → ℝ

  /--
  Nonnegativity of the envelope.
  -/
  h_massEnvelope_nonneg :
    ∀ R : ℝ, 0 ≤ massEnvelope R

  /--
  Exact finite enumerated prime-power mass below cutoff `R` is bounded by the
  envelope.
  -/
  h_exactMass_le_envelope :
    ∀ R : ℝ,
      enumeratedPrimePowerMass massEnum R ≤ massEnvelope R

/--
D-window exact-speed data using a cutoff mass envelope.

Compared with `CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData`, this
removes:

* `massUpper`;
* `h_massUpper_nonneg`;
* `h_exactMass_le_massUpper`.

It replaces them by a cutoff mass envelope and the direct asymptotic

  massEnvelope(R_n) / windowSpeed(coordSet s,n) → 0.
-/
structure CanonicalPrimePowerDWindowMassEnvelopeData
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
  Cutoff mass envelope controlling the exact enumerated prime-power mass.
  -/
  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  /--
  Cutoff mass envelope divided by the actual compact D-window speed tends to
  zero.
  -/
  h_massEnvelope_div_windowSpeed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          massEnvelopeData.massEnvelope ((alpha n).R) /
            windowSpeed.speed (coordSet s) n)
        Filter.atTop
        (𝓝 0)

/--
Convert cutoff mass-envelope data into the previous exact-window-speed envelope
data.
-/
def CanonicalPrimePowerDWindowMassEnvelopeData.toExactWindowSpeedEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassEnvelopeData X) :
    CanonicalPrimePowerDWindowExactWindowSpeedEnvelopeData X :=
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

    massUpper := fun n : ℕ =>
      S.massEnvelopeData.massEnvelope ((S.alpha n).R)

    h_massUpper_nonneg := by
      intro n
      exact S.massEnvelopeData.h_massEnvelope_nonneg ((S.alpha n).R)

    h_exactMass_le_massUpper := by
      intro n
      exact S.massEnvelopeData.h_exactMass_le_envelope ((S.alpha n).R)

    h_massUpper_div_windowSpeed_tendsto_zero := by
      intro s hs
      exact S.h_massEnvelope_div_windowSpeed_tendsto_zero s hs }

/--
Build `CanonicalPrimePowerExhaustionData` from cutoff mass-envelope data.
-/
def CanonicalPrimePowerDWindowMassEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowMassEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toExactWindowSpeedEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` directly from cutoff mass-envelope data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactWindowSpeedEnvelope
    X
    S.toExactWindowSpeedEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once cutoff mass-envelope data is supplied.
-/
theorem canonicalPrimePowerDWindowMassEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowMassEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelope X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowExactWindowSpeedEnvelope_h_Bcan_matches_tsum
      X
      S.toExactWindowSpeedEnvelopeData
      s
      hs

end

end RHFormalization
