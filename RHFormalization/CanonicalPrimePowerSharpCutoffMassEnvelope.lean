import RHFormalization.CanonicalPrimePowerMassUpperEnvelope
import RHFormalization.DCanonicalWindowSharpCutoffConcreteChosenSpeed

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelope

Sharp-cutoff specialization of the D-window mass-envelope package.

This is the first file that feeds the concrete D.CANONICAL-WINDOW sharp-cutoff
compact-speed theorem into the active prime-power D-window mainline.

It removes the generic fields

  W : DCanonicalWindowData
  windowSpeed : DCanonicalWindowCompactSpeedAPI W alpha

by setting

  W := sharpCutoffDCanonicalWindowData G Lstage
  windowSpeed := sharpSpeed.toCompactSpeedAPI.

This is not an endpoint theorem and not another broad wrapper. It connects the
concrete sharp-cutoff compact-speed theorem to the D-side prime-power package.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Sharp-cutoff mass-envelope data.

Compared with `CanonicalPrimePowerDWindowMassEnvelopeData`, this no longer asks
for an arbitrary `W` or arbitrary `windowSpeed`; those are supplied by the
concrete sharp-cutoff construction.
-/
structure CanonicalPrimePowerSharpCutoffMassEnvelopeData
    (X : DFiniteStagePackageFromOperatorLayer) where

  /-- Limiting heat/window kernel. -/
  G : ℝ → ℂ

  /-- Sharp cutoff length attached to each finite stage. -/
  Lstage : DFiniteStage → ℝ

  /-- Stage-selection sequence. -/
  alpha : ℕ → DFiniteStage

  /--
  Concrete sharp-cutoff compact-speed data.

  This supplies the theorem-backed compact-speed API:
  `sharpSpeed.toCompactSpeedAPI`.
  -/
  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha

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
  Structural identification of prime-power kernels with the concrete sharp-cutoff
  D-window kernels.
  -/
  kernelID :
    PrimePowerDWindowKernelIdentificationData
      X
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha
      Kshared

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

  /-- Majorant for the D-window limit kernel. -/
  h_windowLimit_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖(sharpCutoffDCanonicalWindowData G Lstage).G_limit
          (kernelID.coord s q)‖ ≤ kernelMajorant q

  /-- Summable comparison envelope for the weighted majorant. -/
  summabilityEnvelope : PrimePowerPair → ℝ

  /-- Weighted majorant is bounded by the summability envelope. -/
  h_weightedKernelMajorant_le_envelope :
    ∀ q : PrimePowerPair,
      ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q

  /-- The comparison envelope is summable. -/
  h_summabilityEnvelope_summable :
    Summable summabilityEnvelope

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /-- Cutoff mass envelope controlling the exact enumerated prime-power mass. -/
  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  /--
  Cutoff mass envelope divided by the concrete sharp-cutoff compact D-window
  speed tends to zero.
  -/
  h_massEnvelope_div_windowSpeed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          massEnvelopeData.massEnvelope ((alpha n).R) /
            sharpSpeed.toCompactSpeedAPI.speed (coordSet s) n)
        Filter.atTop
        (𝓝 0)

/--
Convert sharp-cutoff mass-envelope data into the existing mass-envelope package.

This is the actual wiring step: the concrete sharp-cutoff speed API is inserted
as the `windowSpeed` field.
-/
def CanonicalPrimePowerSharpCutoffMassEnvelopeData.toMassEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X) :
    CanonicalPrimePowerDWindowMassEnvelopeData X :=
  { W := sharpCutoffDCanonicalWindowData S.G S.Lstage

    alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R :=
      S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R :=
      S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg

    kernelID := S.kernelID
    coordSet := S.coordSet
    h_coordSet_compact := S.h_coordSet_compact
    h_coord_mem := S.h_coord_mem

    windowSpeed := S.sharpSpeed.toCompactSpeedAPI

    h_windowLimit_norm_le_majorant :=
      S.h_windowLimit_norm_le_majorant

    summabilityEnvelope := S.summabilityEnvelope
    h_weightedKernelMajorant_le_envelope :=
      S.h_weightedKernelMajorant_le_envelope
    h_summabilityEnvelope_summable :=
      S.h_summabilityEnvelope_summable

    massEnum := S.massEnum
    massEnvelopeData := S.massEnvelopeData

    h_massEnvelope_div_windowSpeed_tendsto_zero :=
      S.h_massEnvelope_div_windowSpeed_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from sharp-cutoff mass-envelope data.
-/
def CanonicalPrimePowerSharpCutoffMassEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` directly from sharp-cutoff mass-envelope data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffMassEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowMassEnvelope
    X
    S.toMassEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once sharp-cutoff mass-envelope data is supplied.
-/
theorem canonicalPrimePowerSharpCutoffMassEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffMassEnvelope X S).Bcan s =
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
