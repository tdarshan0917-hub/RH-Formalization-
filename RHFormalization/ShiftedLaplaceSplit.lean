import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.ShiftedLaplaceHoloLocalReduction

namespace RHFormalization

noncomputable section

open Complex

theorem shiftedLaplace_split_identity
    (sigma0 : ℝ) (sigmaH : ℝ) :
    ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
      (shiftedLaplacePrimePackageAt sigma0).Bshared s =
        ((shiftedLaplacePrimePackageAt sigma0).Bshared s
          + ZpoleSeries defaultZeroMultiplicityData s)
        - ZpoleSeries defaultZeroMultiplicityData s := by
  intro s _
  ring

#print axioms shiftedLaplace_split_identity

end

end RHFormalization
