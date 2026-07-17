import RHFormalization.CanonicalPrimePowerSharpCutoffClosedDWindowSourceFromFactorBounds

namespace RHFormalization

noncomputable section

def selectedDWindowSoundCountingFactorBoundsData :
    CanonicalPrimePowerDWindowSoundCountingFactorBoundsData
      selectedFiniteOperatorLayer :=
by
  refine
  {
    W :=
      sharpCutoffDCanonicalWindowData
        (heatKernelG (1 : ℝ))
        (fun α : DFiniteStage => α.L)
    alpha := ?alpha
    Kshared := displacementCanonicalKernel (heatKernelG (1 : ℝ))
    h_R_ge_nat := ?h_R_ge_nat
    h_indices_contains_of_center_le_R := ?h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := ?h_indices_subset_center_le_R
    kernelMajorant := ?kernelMajorant
    h_kernelMajorant_nonneg := ?h_kernelMajorant_nonneg
    kernelID := ?kernelID
    coordSet := ?coordSet
    h_coordSet_compact := ?h_coordSet_compact
    h_coord_mem := ?h_coord_mem
    windowSpeed := ?windowSpeed
    h_windowLimit_norm_le_majorant := ?h_windowLimit_norm_le_majorant
    summabilityEnvelope := ?summabilityEnvelope
    h_weightedKernelMajorant_le_envelope := ?h_weightedKernelMajorant_le_envelope
    h_summabilityEnvelope_summable := ?h_summabilityEnvelope_summable
    soundMassCounting := ?soundMassCounting
    denominatorBound := ?denominatorBound
    h_denominatorBound_pos := ?h_denominatorBound_pos
    h_denominatorBound_le_windowSpeed := ?h_denominatorBound_le_windowSpeed
    countBound := ?countBound
    h_countBound_nonneg := ?h_countBound_nonneg
    h_countEnvelope_le_countBound := ?h_countEnvelope_le_countBound
    weightBound := ?weightBound
    h_weightBound_nonneg := ?h_weightBound_nonneg
    h_weightEnvelope_le_weightBound := ?h_weightEnvelope_le_weightBound
    h_countBound_mul_weightBound_div_denominator_tendsto_zero :=
      ?h_countBound_mul_weightBound_div_denominator_tendsto_zero
  }

end

end RHFormalization
