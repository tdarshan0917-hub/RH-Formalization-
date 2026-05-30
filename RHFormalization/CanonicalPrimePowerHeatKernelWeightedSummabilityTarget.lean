import RHFormalization.CanonicalPrimePowerSharpCutoffExactWeightedEnvelope

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

Concrete heat-kernel specialization of the exact weighted-envelope target.

The current sharp-cutoff branch has reduced weighted summability to:

  Summable (displacementWeightedEnvelope G)

i.e.

  Summable (fun q => ‖q.weightC‖ * ‖G q.center‖).

This file fixes the remaining arbitrary `G` by defining the actual
D.CANONICAL-WINDOW heat kernel

  G_t(a) = (4πt)^(-1/2) exp(-a^2/(4t)),

as a complex-valued displacement kernel.

After this file, the remaining theorem is the concrete arithmetic/Gaussian
summability statement:

  Summable (heatKernelWeightedEnvelope t).
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The one-dimensional heat kernel in the displacement variable, complex-valued.

This is the `G_t(a)` from D.CANONICAL-WINDOW:

  G_t(a) = (4πt)^(-1/2) exp(-a^2/(4t)).
-/
noncomputable def heatKernelG (t : ℝ) (a : ℝ) : ℂ :=
  Complex.ofReal
    ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
      Real.exp (-(a ^ 2) / (4 * t)))

/--
The exact weighted envelope for the heat kernel.
-/
noncomputable def heatKernelWeightedEnvelope
    (t : ℝ) :
    PrimePowerPair → ℝ :=
  displacementWeightedEnvelope (heatKernelG t)

/--
The heat-kernel weighted envelope is exactly the current displacement weighted
envelope with `G = heatKernelG t`.
-/
theorem heatKernelWeightedEnvelope_eq
    (t : ℝ) :
    heatKernelWeightedEnvelope t =
      displacementWeightedEnvelope (heatKernelG t) := by
  rfl

/--
Pointwise expanded form of the heat-kernel weighted envelope.
-/
theorem heatKernelWeightedEnvelope_apply
    (t : ℝ)
    (q : PrimePowerPair) :
    heatKernelWeightedEnvelope t q =
      ‖q.weightC‖ * ‖heatKernelG t q.center‖ := by
  rfl

/--
Heat-kernel exact weighted-envelope data.

Compared with `CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData`, this
removes the arbitrary function `G` and fixes it to `heatKernelG t`.

The remaining analytic field is now the concrete theorem:

  Summable (heatKernelWeightedEnvelope t).
-/
structure CanonicalPrimePowerSharpCutoffHeatKernelWeightedData
    (X : DFiniteStagePackageFromOperatorLayer) where

  /-- Heat time. -/
  t : ℝ

  /-- Positivity of the heat time. -/
  ht_pos : 0 < t

  Lstage : DFiniteStage → ℝ
  alpha : ℕ → DFiniteStage

  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData
      (heatKernelG t)
      Lstage
      alpha

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

  kernelID :
    PrimePowerDWindowKernelIdentificationData
      X
      (sharpCutoffDCanonicalWindowData (heatKernelG t) Lstage)
      alpha
      (displacementCanonicalKernel (heatKernelG t))

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
  The concrete remaining summability theorem.
  -/
  h_heatKernelWeightedEnvelope_summable :
    Summable (heatKernelWeightedEnvelope t)

  massEnum : PrimePowerWeightCutoffEnumerationData

  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  hL_chosen :
    ∀ n : ℕ,
      Lstage (alpha n) =
        (massEnvelopeData.massEnvelope ((alpha n).R) + 1) *
          ((n : ℝ) + 1)

/--
Convert heat-kernel weighted data into the previous exact weighted-envelope data.
-/
def CanonicalPrimePowerSharpCutoffHeatKernelWeightedData.toExactWeightedEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffHeatKernelWeightedData X) :
    CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData X :=
  { G := heatKernelG S.t

    Lstage := S.Lstage
    alpha := S.alpha

    sharpSpeed := S.sharpSpeed

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R :=
      S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R :=
      S.h_indices_subset_center_le_R

    kernelID := S.kernelID

    coordSet := S.coordSet
    h_coordSet_compact := S.h_coordSet_compact
    h_coord_mem := S.h_coord_mem

    h_displacementWeightedEnvelope_summable := by
      simpa [heatKernelWeightedEnvelope_eq S.t] using
        S.h_heatKernelWeightedEnvelope_summable

    massEnum := S.massEnum
    massEnvelopeData := S.massEnvelopeData
    hL_chosen := S.hL_chosen }

/--
Build `CanonicalPrimePowerExhaustionData` from heat-kernel weighted data.
-/
def CanonicalPrimePowerSharpCutoffHeatKernelWeightedData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffHeatKernelWeightedData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        (displacementCanonicalKernel (heatKernelG S.t))) :=
  S.toExactWeightedEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` from heat-kernel weighted data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffHeatKernelWeighted
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffHeatKernelWeightedData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffExactWeightedEnvelope
    X
    S.toExactWeightedEnvelopeData

/--
The D-side canonical package matches the concrete heat-kernel tsum package.
-/
theorem canonicalPrimePowerSharpCutoffHeatKernelWeighted_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffHeatKernelWeightedData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffHeatKernelWeighted X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * (displacementCanonicalKernel (heatKernelG S.t)) q.center s := by
  exact
    canonicalPrimePowerSharpCutoffExactWeightedEnvelope_h_Bcan_matches_tsum
      X
      S.toExactWeightedEnvelopeData
      s
      hs

end

end RHFormalization
