import RHFormalization.CanonicalPrimePowerSoundCountingFactorBounds

/-!
# RHFormalization.CanonicalPrimePowerConcreteWeightBound

Concrete weight-bound choice for the current sound-counting factor-bound frontier.

This file removes the next live obstruction

  h_weightEnvelope_le_weightBound

by choosing the stage weight bound to be exactly the existing weight envelope
along the cutoff sequence:

  weightBound n := weightEnvelope ((alpha n).R)

This is the direct field-discharge helper analogous to
`CanonicalPrimePowerConcreteCountBound`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The concrete stage weight bound: use the existing weight envelope evaluated at
the stage cutoff.
-/
noncomputable def concreteWeightBound
    (soundMassCounting : PrimePowerSoundMassCountingSetWeightEnvelopeData)
    (alpha : ℕ → DFiniteStage) :
    ℕ → ℝ :=
  fun n : ℕ =>
    soundMassCounting.weightData.weightEnvelope ((alpha n).R)

/--
The concrete weight bound is nonnegative.
-/
theorem concreteWeightBound_nonneg
    (soundMassCounting : PrimePowerSoundMassCountingSetWeightEnvelopeData)
    (alpha : ℕ → DFiniteStage) :
    ∀ n : ℕ,
      0 ≤ concreteWeightBound soundMassCounting alpha n := by
  intro n
  exact
    soundMassCounting.weightData.h_weightEnvelope_nonneg
      ((alpha n).R)

/--
The active weight-envelope field is discharged by the concrete weight-bound
choice.
-/
theorem weightEnvelope_le_concreteWeightBound
    (soundMassCounting : PrimePowerSoundMassCountingSetWeightEnvelopeData)
    (alpha : ℕ → DFiniteStage) :
    ∀ n : ℕ,
      soundMassCounting.weightData.weightEnvelope ((alpha n).R) ≤
        concreteWeightBound soundMassCounting alpha n := by
  intro n
  exact le_rfl

end

end RHFormalization
