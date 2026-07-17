import RHFormalization.CanonicalPrimePowerSharpCutoffClosedDWindowSourceFromSoundCounting
import RHFormalization.CanonicalPrimePowerSoundCountingFactorBounds
import RHFormalization.SelectedFiniteOperatorLayer

/-!
# Closed D-window source from sound-counting factor bounds

This is a mechanical bridge.

The actual source object is:

`CanonicalPrimePowerDWindowSoundCountingFactorBoundsData selectedFiniteOperatorLayer`.

It converts by:

`toSoundCountingData`
then
`toMassCountingSetWeightEnvelopeData`.
-/

namespace RHFormalization

noncomputable section

def buildSelectedSharpCutoffClosedDWindowSourceFromFactorBounds
    (Sfb :
      CanonicalPrimePowerDWindowSoundCountingFactorBoundsData
        selectedFiniteOperatorLayer)
    (hW :
      Sfb.W =
        sharpCutoffDCanonicalWindowData
          (heatKernelG (1 : ℝ))
          (fun α : DFiniteStage => α.L))
    (hKshared :
      Sfb.Kshared =
        displacementCanonicalKernel (heatKernelG (1 : ℝ)))
    (sharpSpeed :
      DCanonicalWindowSharpCutoffConcreteChosenSpeedData
        (heatKernelG (1 : ℝ))
        (fun α : DFiniteStage => α.L)
        Sfb.alpha)
    (hL_chosen :
      ∀ n : ℕ,
        (Sfb.alpha n).L =
          ((exactPrimePowerMassEnvelopeData
                Sfb.soundMassCounting.soundEnum.massEnum).massEnvelope
              (Sfb.alpha n).R + 1) *
            ((n : ℝ) + 1)) :
    SelectedSharpCutoffClosedDWindowSource :=
  buildSelectedSharpCutoffClosedDWindowSourceFromSoundCounting
    Sfb.toSoundCountingData
    (by
      simpa [CanonicalPrimePowerDWindowSoundCountingFactorBoundsData.toSoundCountingData]
        using hW)
    (by
      simpa [CanonicalPrimePowerDWindowSoundCountingFactorBoundsData.toSoundCountingData]
        using hKshared)
    (by
      simpa [CanonicalPrimePowerDWindowSoundCountingFactorBoundsData.toSoundCountingData]
        using sharpSpeed)
    (by
      intro n
      simpa [CanonicalPrimePowerDWindowSoundCountingFactorBoundsData.toSoundCountingData]
        using hL_chosen n)

end

end RHFormalization
