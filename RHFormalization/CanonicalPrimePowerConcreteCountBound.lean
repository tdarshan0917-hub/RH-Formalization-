import RHFormalization.CanonicalPrimePowerSoundCountingFactorBounds

/-!
# RHFormalization.CanonicalPrimePowerConcreteCountBound

Concrete count-bound choice for the current sound-counting factor-bound frontier.

This file removes the first live obstruction

  h_countEnvelope_le_countBound

by choosing the stage count bound to be exactly the existing count envelope along
the cutoff sequence:

  countBound n := countEnvelope ((alpha n).R)

This is not a new endpoint. It is the direct field-discharge helper for the
first active factor-bound field.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The concrete stage count bound: use the existing count envelope evaluated at
the stage cutoff.
-/
noncomputable def concreteCountBound
    (soundMassCounting : PrimePowerSoundMassCountingSetWeightEnvelopeData)
    (alpha : ℕ → DFiniteStage) :
    ℕ → ℝ :=
  fun n : ℕ =>
    soundMassCounting.centerCountingSet.countEnvelope ((alpha n).R)

/--
The concrete count bound is nonnegative.
-/
theorem concreteCountBound_nonneg
    (soundMassCounting : PrimePowerSoundMassCountingSetWeightEnvelopeData)
    (alpha : ℕ → DFiniteStage) :
    ∀ n : ℕ,
      0 ≤ concreteCountBound soundMassCounting alpha n := by
  intro n
  exact
    soundMassCounting.centerCountingSet.h_countEnvelope_nonneg
      ((alpha n).R)

/--
The active count-envelope field is discharged by the concrete count-bound
choice.
-/
theorem countEnvelope_le_concreteCountBound
    (soundMassCounting : PrimePowerSoundMassCountingSetWeightEnvelopeData)
    (alpha : ℕ → DFiniteStage) :
    ∀ n : ℕ,
      soundMassCounting.centerCountingSet.countEnvelope ((alpha n).R) ≤
        concreteCountBound soundMassCounting alpha n := by
  intro n
  exact le_rfl

end

end RHFormalization
