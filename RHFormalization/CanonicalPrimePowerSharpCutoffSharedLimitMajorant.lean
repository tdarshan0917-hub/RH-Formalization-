import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffSharedLimitMajorant

Shared-kernel form of the sharp-cutoff window-limit majorant.

The latest audit shows:

* `sharpCutoffDCanonicalWindowData G Lstage` has `G_limit := G`;
* `PrimePowerDWindowKernelIdentificationData` contains
  `h_shared_kernel_eq_limit :
     Kshared q.center s = W.G_limit (coord s q)`.

Therefore the correct next reduction is to replace the field

  ‖W.G_limit (kernelID.coord s q)‖ ≤ kernelMajorant q

by the shared-kernel estimate

  ‖Kshared q.center s‖ ≤ kernelMajorant q.

This file removes the direct `h_windowLimit_norm_le_majorant` field from the
chosen-length sharp-cutoff branch and derives it from the shared-kernel bound.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A shared-kernel majorant implies the D-window-limit majorant, using the kernel
identification equality

  Kshared q.center s = W.G_limit (coord s q).
-/
theorem windowLimit_norm_le_majorant_of_sharedKernel_norm_le
    {X : DFiniteStagePackageFromOperatorLayer}
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    (kernelID :
      PrimePowerDWindowKernelIdentificationData
        X
        (sharpCutoffDCanonicalWindowData G Lstage)
        alpha
        Kshared)
    (kernelMajorant : PrimePowerPair → ℝ)
    (h_sharedKernel_norm_le_majorant :
      ∀ s : ℂ,
      ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      ∀ q : PrimePowerPair,
        ‖Kshared q.center s‖ ≤ kernelMajorant q) :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖(sharpCutoffDCanonicalWindowData G Lstage).G_limit
          (kernelID.coord s q)‖ ≤ kernelMajorant q := by
  intro s hs q
  have hID :
      Kshared q.center s =
        (sharpCutoffDCanonicalWindowData G Lstage).G_limit
          (kernelID.coord s q) :=
    kernelID.h_shared_kernel_eq_limit s hs q
  simpa [hID] using
    h_sharedKernel_norm_le_majorant s hs q

/--
Chosen-length sharp-cutoff mass-envelope data where the D-window-limit majorant
is derived from the shared-kernel majorant.

Compared with `CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData`, this
removes the field:

  h_windowLimit_norm_le_majorant

and replaces it with:

  h_sharedKernel_norm_le_majorant.
-/
structure CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData
    (X : DFiniteStagePackageFromOperatorLayer) where

  G : ℝ → ℂ
  Lstage : DFiniteStage → ℝ
  alpha : ℕ → DFiniteStage

  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha

  Kshared : CanonicalKernelC

  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  h_indices_subset_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        q.center ≤ (alpha n).R

  kernelMajorant : PrimePowerPair → ℝ

  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  kernelID :
    PrimePowerDWindowKernelIdentificationData
      X
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha
      Kshared

  coordSet : ℂ → Set ℝ

  h_coordSet_compact :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  h_coord_mem :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        kernelID.coord s q ∈ coordSet s

  /--
  Shared-kernel majorant.

  This is the mathematically natural analytic estimate.
  The D-window-limit majorant is derived from this using `kernelID`.
  -/
  h_sharedKernel_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖Kshared q.center s‖ ≤ kernelMajorant q

  summabilityEnvelope : PrimePowerPair → ℝ

  h_weightedKernelMajorant_le_envelope :
    ∀ q : PrimePowerPair,
      ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q

  h_summabilityEnvelope_summable :
    Summable summabilityEnvelope

  massEnum : PrimePowerWeightCutoffEnumerationData

  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  hL_chosen :
    ∀ n : ℕ,
      Lstage (alpha n) =
        (massEnvelopeData.massEnvelope ((alpha n).R) + 1) *
          ((n : ℝ) + 1)

/--
Convert shared-majorant data into the chosen-length mass-envelope package.
This is where `h_windowLimit_norm_le_majorant` is discharged.
-/
def CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData.toChosenLengthMassEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData X) :
    CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X :=
  { G := S.G
    Lstage := S.Lstage
    alpha := S.alpha
    sharpSpeed := S.sharpSpeed
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

    h_windowLimit_norm_le_majorant :=
      windowLimit_norm_le_majorant_of_sharedKernel_norm_le
        S.kernelID
        S.kernelMajorant
        S.h_sharedKernel_norm_le_majorant

    summabilityEnvelope := S.summabilityEnvelope
    h_weightedKernelMajorant_le_envelope :=
      S.h_weightedKernelMajorant_le_envelope
    h_summabilityEnvelope_summable :=
      S.h_summabilityEnvelope_summable

    massEnum := S.massEnum
    massEnvelopeData := S.massEnvelopeData
    hL_chosen := S.hL_chosen }

/--
Build `CanonicalPrimePowerExhaustionData` from shared-majorant chosen-length data.
-/
def CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toChosenLengthMassEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` from shared-majorant chosen-length data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffChosenLengthSharedMajorant
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
    X
    S.toChosenLengthMassEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once shared-majorant chosen-length sharp-cutoff data is supplied.
-/
theorem canonicalPrimePowerSharpCutoffChosenLengthSharedMajorant_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthSharedMajorantData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffChosenLengthSharedMajorant X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerSharpCutoffChosenLengthMassEnvelope_h_Bcan_matches_tsum
      X
      S.toChosenLengthMassEnvelopeData
      s
      hs

end

end RHFormalization
