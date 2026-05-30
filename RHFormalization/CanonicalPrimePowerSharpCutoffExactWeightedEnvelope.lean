import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffExactWeightedEnvelope

Exact weighted envelope for the sharp-cutoff displacement-kernel branch.

The previous file specialized the shared kernel to

  Kshared a s := G a

and chose

  kernelMajorant q := ‖G q.center‖.

This file removes the arbitrary weighted comparison envelope by choosing

  summabilityEnvelope q := ‖q.weightC‖ * ‖G q.center‖.

So the field

  h_weightedKernelMajorant_le_envelope

is discharged by `le_rfl`.

The only remaining analytic summability target is then the real one:

  Summable (fun q => ‖q.weightC‖ * ‖G q.center‖).
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The exact weighted displacement-kernel envelope.
-/
def displacementWeightedEnvelope
    (G : ℝ → ℂ)
    (q : PrimePowerPair) : ℝ :=
  ‖q.weightC‖ * displacementKernelMajorant G q

/--
The exact weighted envelope bounds the weighted kernel majorant by reflexivity.
-/
theorem displacementWeightedEnvelope_le
    (G : ℝ → ℂ) :
    ∀ q : PrimePowerPair,
      ‖q.weightC‖ * displacementKernelMajorant G q
        ≤ displacementWeightedEnvelope G q := by
  intro q
  exact le_rfl

/--
Sharp-cutoff displacement-kernel data with the exact weighted envelope.

Compared with
`CanonicalPrimePowerSharpCutoffChosenLengthDisplacementKernelData`, this removes:

* `summabilityEnvelope`;
* `h_weightedKernelMajorant_le_envelope`.

It replaces them by the exact summability theorem:

  Summable (fun q => ‖q.weightC‖ * ‖G q.center‖).
-/
structure CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData
    (X : DFiniteStagePackageFromOperatorLayer) where

  G : ℝ → ℂ
  Lstage : DFiniteStage → ℝ
  alpha : ℕ → DFiniteStage

  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha

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
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha
      (displacementCanonicalKernel G)

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
  The true remaining weighted summability theorem for the displacement kernel.
  -/
  h_displacementWeightedEnvelope_summable :
    Summable (displacementWeightedEnvelope G)

  massEnum : PrimePowerWeightCutoffEnumerationData

  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  hL_chosen :
    ∀ n : ℕ,
      Lstage (alpha n) =
        (massEnvelopeData.massEnvelope ((alpha n).R) + 1) *
          ((n : ℝ) + 1)

/--
Convert exact-envelope data into the displacement-kernel branch.

This is where the old arbitrary weighted-envelope fields are discharged.
-/
def CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData.toDisplacementKernelData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData X) :
    CanonicalPrimePowerSharpCutoffChosenLengthDisplacementKernelData X :=
  { G := S.G
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

    summabilityEnvelope := displacementWeightedEnvelope S.G

    h_weightedKernelMajorant_le_envelope :=
      displacementWeightedEnvelope_le S.G

    h_summabilityEnvelope_summable :=
      S.h_displacementWeightedEnvelope_summable

    massEnum := S.massEnum
    massEnvelopeData := S.massEnvelopeData
    hL_chosen := S.hL_chosen }

/--
Build `CanonicalPrimePowerExhaustionData` from exact weighted-envelope data.
-/
def CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        (displacementCanonicalKernel S.G)) :=
  S.toDisplacementKernelData.toExhaustionData

/--
Build `DBcanLimitData` from exact weighted-envelope data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffExactWeightedEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffChosenLengthDisplacementKernel
    X
    S.toDisplacementKernelData

/--
The D-side canonical package matches the concrete displacement-kernel tsum package.
-/
theorem canonicalPrimePowerSharpCutoffExactWeightedEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffExactWeightedEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffExactWeightedEnvelope X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * (displacementCanonicalKernel S.G) q.center s := by
  exact
    canonicalPrimePowerSharpCutoffChosenLengthDisplacementKernel_h_Bcan_matches_tsum
      X
      S.toDisplacementKernelData
      s
      hs

end

end RHFormalization
