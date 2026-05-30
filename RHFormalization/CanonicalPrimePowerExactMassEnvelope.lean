import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope

/-!
# RHFormalization.CanonicalPrimePowerExactMassEnvelope

Exact mass envelope for prime-power cutoff mass.

This removes the artificial envelope estimate

  PrimePowerMassEnvelopeData.h_exactMass_le_envelope

by choosing the mass envelope itself to be the exact enumerated mass:

  massEnvelope R := enumeratedPrimePowerMass massEnum R.

This is not an endpoint and not a wrapper around RH. It kills one concrete field.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The exact enumerated mass is itself a valid mass envelope.
-/
def exactPrimePowerMassEnvelopeData
    (massEnum : PrimePowerWeightCutoffEnumerationData) :
    PrimePowerMassEnvelopeData massEnum :=
  { massEnvelope := fun R : ℝ =>
      enumeratedPrimePowerMass massEnum R

    h_massEnvelope_nonneg := by
      intro R
      exact enumeratedPrimePowerMass_nonneg massEnum R

    h_exactMass_le_envelope := by
      intro R
      rfl }

/--
A named theorem form of the exact-envelope estimate.
-/
theorem exactPrimePowerMassEnvelope_exactMass_le
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    enumeratedPrimePowerMass massEnum R ≤
      (exactPrimePowerMassEnvelopeData massEnum).massEnvelope R := by
  rfl

/--
A named theorem form of exact-envelope nonnegativity.
-/
theorem exactPrimePowerMassEnvelope_nonneg
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    0 ≤ (exactPrimePowerMassEnvelopeData massEnum).massEnvelope R := by
  exact enumeratedPrimePowerMass_nonneg massEnum R

end

end RHFormalization
