import RHFormalization.ShiftedLaplaceModelPP
import RHFormalization.ShiftedLaplaceZpoleWiring
import RHFormalization.PrincipalPartEventuallyEq
import RHFormalization.CanonicalPrimePowerTsumPrincipalPart
import RHFormalization.ShiftedLaplaceDSharedBridge

namespace RHFormalization

noncomputable section

open Complex Filter Topology

def ShiftedLaplaceBridgeData (sigma0 : ℝ) : Prop :=
  ∀ W : ZeroWitness,
    ∀ᶠ w in 𝓝 W.s0, w ≠ W.s0 →
      (shiftedLaplacePrimePackageAt sigma0).Bshared w
        = shiftedLaplaceLogDerivModel w

theorem shiftedLaplace_hBpp_from_bridge
    (sigma0 : ℝ)
    (hbridge : ShiftedLaplaceBridgeData sigma0) :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0
        (-(groupedResidueCoeff defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W))) := by
  intro W
  have hmodel := shiftedLaplaceLogDerivModel_principalPart_at_witness W
  have hcoeff :
      (-(groupedResidueCoeff defaultZeroMultiplicityData
          (defaultGroupedPoleClass defaultZeroMultiplicityData W)))
        = (-(zetaZeroMult W.ρ : ℂ)) := by
    rw [groupedResidueCoeff_default_eq_zetaZeroMult]
  rw [hcoeff]
  exact hasPrincipalPart_of_eventuallyEq (hbridge W) hmodel

#print axioms shiftedLaplace_hBpp_from_bridge

end

end RHFormalization
