import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayloadFromHeatKernelWeighted
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityClosure

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedDataClosedSummability

Constructor for `CanonicalPrimePowerSharpCutoffHeatKernelWeightedData` with the
heat-kernel weighted-envelope summability field discharged by the closed theorem
`heatKernelWeightedEnvelope_summable`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the heat-kernel weighted sharp-cutoff package with the summability field
filled by the closed heat-kernel summability theorem.
-/
def buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataClosedSummability
    (X : DFiniteStagePackageFromOperatorLayer)
    (t : ℝ)
    (ht_pos : 0 < t)
    (Lstage : DFiniteStage → ℝ)
    (alpha : ℕ → DFiniteStage)
    (sharpSpeed :
      DCanonicalWindowSharpCutoffConcreteChosenSpeedData
        (heatKernelG t)
        Lstage
        alpha)
    (h_R_ge_nat :
      ∀ (n : ℕ), (n : ℝ) ≤ (alpha n).R)
    (h_indices_contains_of_center_le_R :
      ∀ (n : ℕ) (q : PrimePowerPair),
        IsPrimePowerPair q →
        q.center ≤ (alpha n).R →
          q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
    (h_indices_subset_center_le_R :
      ∀ (n : ℕ),
        ∀ q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n),
          q.center ≤ (alpha n).R)
    (kernelID :
      PrimePowerDWindowKernelIdentificationData
        X
        (sharpCutoffDCanonicalWindowData (heatKernelG t) Lstage)
        alpha
        (displacementCanonicalKernel (heatKernelG t)))
    (coordSet : ℂ → Set ℝ)
    (h_coordSet_compact :
      ∀ s ∈ RightHalfPlane X.toStagePackage.sigma0,
        IsCompact (coordSet s))
    (h_coord_mem :
      ∀ s ∈ RightHalfPlane X.toStagePackage.sigma0,
        ∀ (n : ℕ),
          ∀ q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n),
            kernelID.coord s q ∈ coordSet s)
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (massEnvelopeData : PrimePowerMassEnvelopeData massEnum)
    (hL_chosen :
      ∀ (n : ℕ),
        Lstage (alpha n) =
          (massEnvelopeData.massEnvelope (alpha n).R + 1) * ((n : ℝ) + 1)) :
    CanonicalPrimePowerSharpCutoffHeatKernelWeightedData X :=
  { t := t
    ht_pos := ht_pos
    Lstage := Lstage
    alpha := alpha
    sharpSpeed := sharpSpeed
    h_R_ge_nat := h_R_ge_nat
    h_indices_contains_of_center_le_R := h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := h_indices_subset_center_le_R
    kernelID := kernelID
    coordSet := coordSet
    h_coordSet_compact := h_coordSet_compact
    h_coord_mem := h_coord_mem
    h_heatKernelWeightedEnvelope_summable :=
      heatKernelWeightedEnvelope_summable t ht_pos
    massEnum := massEnum
    massEnvelopeData := massEnvelopeData
    hL_chosen := hL_chosen }

end

end RHFormalization
