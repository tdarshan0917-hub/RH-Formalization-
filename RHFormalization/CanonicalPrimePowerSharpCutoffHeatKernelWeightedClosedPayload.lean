import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedDataClosedSummability

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload

Payload boundary for building `CanonicalPrimePowerSharpCutoffHeatKernelWeightedData`
after the heat-kernel weighted summability field has been discharged by
`heatKernelWeightedEnvelope_summable`.

This names the remaining selected-H0 inputs.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The remaining payload needed to build the selected heat-kernel weighted
sharp-cutoff package once summability is closed.
-/
structure CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload where
  X : DFiniteStagePackageFromOperatorLayer

  t : ℝ
  ht_pos : 0 < t

  Lstage : DFiniteStage → ℝ
  alpha : ℕ → DFiniteStage

  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData
      (heatKernelG t)
      Lstage
      alpha

  h_R_ge_nat :
    ∀ (n : ℕ), (n : ℝ) ≤ (alpha n).R

  h_indices_contains_of_center_le_R :
    ∀ (n : ℕ) (q : PrimePowerPair),
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  h_indices_subset_center_le_R :
    ∀ (n : ℕ),
      ∀ q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n),
        q.center ≤ (alpha n).R

  kernelID :
    PrimePowerDWindowKernelIdentificationData
      X
      (sharpCutoffDCanonicalWindowData (heatKernelG t) Lstage)
      alpha
      (displacementCanonicalKernel (heatKernelG t))

  coordSet : ℂ → Set ℝ

  h_coordSet_compact :
    ∀ s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  h_coord_mem :
    ∀ s ∈ RightHalfPlane X.toStagePackage.sigma0,
      ∀ (n : ℕ),
        ∀ q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n),
          kernelID.coord s q ∈ coordSet s

  massEnum : PrimePowerWeightCutoffEnumerationData

  massEnvelopeData :
    PrimePowerMassEnvelopeData massEnum

  hL_chosen :
    ∀ (n : ℕ),
      Lstage (alpha n) =
        (massEnvelopeData.massEnvelope (alpha n).R + 1) * ((n : ℝ) + 1)

/--
Build `CanonicalPrimePowerSharpCutoffHeatKernelWeightedData` from the closed
payload. The summability field is supplied by
`heatKernelWeightedEnvelope_summable`.
-/
def CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload.toHeatKernelWeightedData
    (P : CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload) :
    CanonicalPrimePowerSharpCutoffHeatKernelWeightedData P.X :=
  buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataClosedSummability
    P.X
    P.t
    P.ht_pos
    P.Lstage
    P.alpha
    P.sharpSpeed
    P.h_R_ge_nat
    P.h_indices_contains_of_center_le_R
    P.h_indices_subset_center_le_R
    P.kernelID
    P.coordSet
    P.h_coordSet_compact
    P.h_coord_mem
    P.massEnum
    P.massEnvelopeData
    P.hL_chosen

/--
Direct constructor from the named closed payload.
-/
def buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataFromClosedPayload
    (P : CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload) :
    CanonicalPrimePowerSharpCutoffHeatKernelWeightedData P.X :=
  P.toHeatKernelWeightedData

end

end RHFormalization
