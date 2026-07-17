import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.PrimePerturbedFStage
import RHFormalization.ArithmeticShiftedLaplaceBStageFiniteCanonical
import RHFormalization.ResolventStageHolo
import RHFormalization.DMasterResidualAlong
import Mathlib

/-!
# Conditional DMasterResidualData for the aligned prime-perturbed layer

This file wires the aligned operator layer to `DMasterResidualData`.
It does not prove D.CAN-REM. It isolates the remaining full h_conv input.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- Stage holomorphy for the aligned prime-perturbed layer.

Aligned B is `arithmeticShiftedLaplaceBStage`, not the old payload's
`finiteCanonicalPrimePowerPackage (resolventIndices α) ...`.
-/
theorem primePerturbedAligned_stage_holo
    {N : ℕ} (μ : Fin N → ℝ)
    (hpos :
      ∀ α : DFiniteStage,
      ∀ i,
        0 ≤ perturbedEigenvalues μ
          (primePotential_isHermitian
            (primeStageWeights (primePerturbedStageIndex α))) i) :
    ∀ α : DFiniteStage,
      HolomorphicOnC
        (fun s =>
          (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s) Ω := by
  intro α

  have hF : HolomorphicOnC
      (fun s =>
        primePerturbedFStage μ
          (primeStageWeights (primePerturbedStageIndex α)) s) Ω :=
    primePerturbedFStage_holo
      μ
      (primeStageWeights (primePerturbedStageIndex α))
      (hpos α)

  have hBfinite : HolomorphicOnC
      (fun s =>
        finiteCanonicalPrimePowerPackage
          (α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP)
          shiftedLaplaceHeatKernelC
          s) Ω := by
    apply holomorphicOnC_of_forall_holomorphicAtC
    intro s hs
    exact
      finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
        (α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP)
        s
        hs

  have hBeq :
      (fun s => arithmeticShiftedLaplaceBStage α s)
        =
      (fun s =>
        finiteCanonicalPrimePowerPackage
          (α.diagonalSpikeActiveIndices.image α.diagonalSpikeToPP)
          shiftedLaplaceHeatKernelC
          s) := by
    funext s
    exact arithmeticShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image α s

  have hB : HolomorphicOnC
      (fun s => arithmeticShiftedLaplaceBStage α s) Ω := by
    rw [hBeq]
    exact hBfinite

  simpa [primePerturbedOperatorLayerAligned, primePerturbedPayloadAligned] using
    hF.sub hB

/-- Conditional aligned R object. The real remaining input is full Ω h_conv. -/
def primePerturbedDMasterResidualAligned_from_inputs
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (R_H : ℂ → ℂ)
    (hpos :
      ∀ α : DFiniteStage,
      ∀ i,
        0 ≤ perturbedEigenvalues μ
          (primePotential_isHermitian
            (primeStageWeights (primePerturbedStageIndex α))) i)
    (h_conv :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∀ ε : ℝ,
            0 < ε →
              ∀ᶠ n in Filter.atTop,
                ∀ s : ℂ,
                  s ∈ K →
                    dist
                      ((primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                        (alpha n) s)
                      (R_H s) < ε) :
    DMasterResidualData
      (primePerturbedOperatorLayerAligned μ).toStagePackage :=
  buildDMasterResidualDataAlong
    (primePerturbedOperatorLayerAligned μ).toStagePackage
    alpha
    R_H
    (fun n => primePerturbedAligned_stage_holo μ hpos (alpha n))
    h_conv

#print axioms primePerturbedAligned_stage_holo
#print axioms primePerturbedDMasterResidualAligned_from_inputs

end
end RHFormalization
