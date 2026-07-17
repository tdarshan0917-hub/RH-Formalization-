import RHFormalization.DesignedOperatorLayer
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.CanonicalPrimePowerRCutoffExhaustion
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel

/-!
# RHFormalization.DesignedRCutoffS

The concrete R-cutoff mass-growth/window instance over the designed operator
layer and the prime-power stage ladder. Window error is identically zero
(stage kernel = shared kernel = displacement Gaussian); mass growth is the
exact enumerated mass; weighted-majorant summability is the banked Gaussian
core theorem.
-/

namespace RHFormalization

noncomputable section

open Complex

/-- The designed layer's formula indices at a prime-power stage collapse to
the concrete enumeration. -/
theorem designed_indices_primePowerStage (n : ℕ) :
    designedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
        (primePowerStage n) =
      concretePrimePowerBelowCutoff ((n : ℝ) + 1) := by
  show ((primePowerStage n).diagonalSpikeActiveIndices).image
        ((primePowerStage n).diagonalSpikeToPP) =
      concretePrimePowerBelowCutoff ((n : ℝ) + 1)
  show (ppStageCodes n).image ppDecode =
      concretePrimePowerBelowCutoff ((n : ℝ) + 1)
  unfold ppStageCodes
  rw [Finset.image_image]
  have hcomp : ppDecode ∘ ppCode = id := funext ppDecode_ppCode
  rw [hcomp, Finset.image_id]

/-- The designed layer's formula kernel is the constant displacement Gaussian. -/
theorem designed_kernel_eq (α : DFiniteStage) :
    designedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.kernel α =
      displacementCanonicalKernel (heatKernelG 1) := by
  rfl

/-- The concrete S-instance over the designed layer and the prime-power ladder. -/
noncomputable def designedRCutoffS :
    CanonicalPrimePowerRCutoffMassGrowthWindowData designedFiniteOperatorLayer :=
  { alpha := primePowerStage
    Kshared := displacementCanonicalKernel (heatKernelG 1)
    h_R_tendsto_atTop := primePowerStage_R_tendsto_atTop
    h_indices_contains_of_center_le_R := by
      intro n q hq hle
      rw [designed_indices_primePowerStage n]
      exact concretePrimePowerEnum.h_mem_belowCutoff ((n : ℝ) + 1) q hq
        (by simpa [primePowerStage] using hle)
    kernelMajorant := fun q => ‖heatKernelG 1 q.center‖
    h_kernelMajorant_nonneg := by intro q; exact norm_nonneg _
    h_sharedKernel_norm_le_majorant := by
      intro s _ q
      simp [displacementCanonicalKernel]
    h_weightedKernelMajorant_summable := by
      have hcore := heatKernelGaussianCoreEnvelope_summable 1 one_pos
      have henv := heatKernelWeightedEnvelope_summable_of_core 1 one_pos hcore
      have hEq :
          (fun q : PrimePowerPair => ‖q.weightC‖ * ‖heatKernelG 1 q.center‖) =
            heatKernelWeightedEnvelope 1 := by
        funext q
        first
          | rfl
          | simp [heatKernelWeightedEnvelope]
          | rw [heatKernelWeightedEnvelope_apply]
      rw [hEq]
      exact henv
    windowError := fun _ _ => 0
    h_windowError_nonneg := by intro s _ n; exact le_refl 0
    massGrowth := fun n =>
      (designedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
        (primePowerStage n)).sum (fun q => ‖q.weightC‖)
    h_massGrowth_nonneg := by
      intro n
      exact Finset.sum_nonneg (fun q _ => norm_nonneg q.weightC)
    h_weightC_mass_le_growth := by intro n; exact le_refl _
    h_massGrowth_window_tendsto_zero := by
      intro s _
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
        Filter.atTop (nhds 0))
    h_kernel_window_error_le := by
      intro s _ n q _
      rw [designed_kernel_eq]
      simp }

#print axioms designedRCutoffS

end

end RHFormalization
