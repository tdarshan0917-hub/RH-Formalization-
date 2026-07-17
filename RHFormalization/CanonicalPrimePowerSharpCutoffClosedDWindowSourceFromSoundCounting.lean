import RHFormalization.CanonicalPrimePowerSharpCutoffClosedDWindowSource
import RHFormalization.CanonicalPrimePowerSoundCutoffCounting
import RHFormalization.SelectedFiniteOperatorLayer

/-!
# Closed D-window source from sound-counting data

This file fixes the previous naming mistake.

The real upstream structure is:

`CanonicalPrimePowerDWindowSoundCountingData`

not:

`CanonicalPrimePowerSoundCutoffCountingData`.

It converts to the required `S` field by:

`CanonicalPrimePowerDWindowSoundCountingData.toMassCountingSetWeightEnvelopeData`.
-/

namespace RHFormalization

noncomputable section

def buildSelectedSharpCutoffClosedDWindowSourceFromSoundCounting
    (Ssound :
      CanonicalPrimePowerDWindowSoundCountingData selectedFiniteOperatorLayer)
    (hW :
      Ssound.W =
        sharpCutoffDCanonicalWindowData
          (heatKernelG (1 : ℝ))
          (fun α : DFiniteStage => α.L))
    (hKshared :
      Ssound.Kshared =
        displacementCanonicalKernel (heatKernelG (1 : ℝ)))
    (sharpSpeed :
      DCanonicalWindowSharpCutoffConcreteChosenSpeedData
        (heatKernelG (1 : ℝ))
        (fun α : DFiniteStage => α.L)
        Ssound.alpha)
    (hL_chosen :
      ∀ n : ℕ,
        (Ssound.alpha n).L =
          ((exactPrimePowerMassEnvelopeData
                Ssound.soundMassCounting.soundEnum.massEnum).massEnvelope
              (Ssound.alpha n).R + 1) *
            ((n : ℝ) + 1)) :
    SelectedSharpCutoffClosedDWindowSource :=
{
  S := Ssound.toMassCountingSetWeightEnvelopeData

  hW := by
    simpa [CanonicalPrimePowerDWindowSoundCountingData.toMassCountingSetWeightEnvelopeData]
      using hW

  hKshared := by
    simpa [CanonicalPrimePowerDWindowSoundCountingData.toMassCountingSetWeightEnvelopeData]
      using hKshared

  sharpSpeed := by
    simpa [CanonicalPrimePowerDWindowSoundCountingData.toMassCountingSetWeightEnvelopeData]
      using sharpSpeed

  hL_chosen := by
    intro n
    simpa [CanonicalPrimePowerDWindowSoundCountingData.toMassCountingSetWeightEnvelopeData]
      using hL_chosen n
}

end

end RHFormalization
