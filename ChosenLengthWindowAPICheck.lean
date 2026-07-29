import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromFR
import RHFormalization.DCanonicalWindowSharpCutoffConcreteChosenSpeed
import RHFormalization.DCanonicalWindowSharpCutoffConcrete
import RHFormalization.DCanonicalWindowConcrete

namespace RHFormalization

variable (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)

#check sharpCutoffDCanonicalWindowData S.G S.Lstage
#check S.sharpSpeed
#check S.sharpSpeed.toCompactSpeedAPI

-- Test whether the speed API directly gives the Wapi we need.
#check
  (S.sharpSpeed.toCompactSpeedAPI :
    DCanonicalWindowAPI (sharpCutoffDCanonicalWindowData S.G S.Lstage))

-- Test alpha alignment for Wapi.
example :
    (S.sharpSpeed.toCompactSpeedAPI :
      DCanonicalWindowAPI (sharpCutoffDCanonicalWindowData S.G S.Lstage)).alpha = S.alpha := by
  rfl

end RHFormalization
