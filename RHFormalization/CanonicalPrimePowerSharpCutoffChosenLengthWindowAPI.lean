import RHFormalization.DCanonicalWindowAPIFromCompactSpeed
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthWindowAPI

Window-data and window-API helpers for the chosen-length sharp-cutoff route.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/-- The selected chosen-length sharp-cutoff window data. -/
def chosenLengthWindowData
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer) :
    DCanonicalWindowData :=
  sharpCutoffDCanonicalWindowData S.G S.Lstage

/--
Build the selected chosen-length window API from the compact-speed API, assuming
the inverse chosen speed tends to zero on every compact real set.
-/
def chosenLengthWindowAPI_of_invSpeed
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (h_inv_speed_tendsto_zero :
      ∀ (K : Set ℝ),
        IsCompact K →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                (1 : ℝ) / S.sharpSpeed.toCompactSpeedAPI.speed K n < ε) :
    DCanonicalWindowAPI (chosenLengthWindowData finiteOperatorLayer S) :=
  buildDCanonicalWindowAPIFromCompactSpeed
    S.sharpSpeed.toCompactSpeedAPI
    (by rfl)
    h_inv_speed_tendsto_zero

theorem chosenLengthWindowAPI_alpha
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (h_inv_speed_tendsto_zero :
      ∀ (K : Set ℝ),
        IsCompact K →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                (1 : ℝ) / S.sharpSpeed.toCompactSpeedAPI.speed K n < ε) :
    (chosenLengthWindowAPI_of_invSpeed
      finiteOperatorLayer S h_inv_speed_tendsto_zero).alpha = S.alpha := by
  rfl

end

end RHFormalization
