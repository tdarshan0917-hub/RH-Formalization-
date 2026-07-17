import RHFormalization.ShiftedLaplaceRepWitness
import RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts
import RHFormalization.ShiftedLaplaceBppFromBridge

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem shiftedLaplace_repWitness_from_principalParts
    (sigma0 : ℝ)
    (hBpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
          W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (hpoint :
      ∀ W : ZeroWitness,
        (Classical.choose (hBpp W)) W.s0 +
          (Classical.choose (hZpp_rep W)) W.s0 =
            (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0 +
              ZpoleRepSeries defaultZeroMultiplicityData W.s0) :
    ∀ W : ZeroWitness,
      ∃ h : ℂ → ℂ,
        HolomorphicAtC h W.s0 ∧
          LocalEqAtC h
            (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
              + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 := by
  apply shiftedLaplace_repWitness_extension sigma0
  intro W
  exact witnessCancellationData_from_opposite_principalParts
    (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
    (ZpoleRepSeries defaultZeroMultiplicityData)
    W (zetaZeroMult W.ρ : ℂ) (hBpp W) (hZpp_rep W) (hpoint W)

theorem shiftedLaplace_hBpp_singleton_from_bridge
    (sigma0 : ℝ)
    (hbridge : ShiftedLaplaceBridgeData sigma0) :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)) := by
  intro W
  have h := shiftedLaplace_hBpp_from_bridge sigma0 hbridge W
  rwa [groupedResidueCoeff_default_eq_zetaZeroMult] at h

#print axioms shiftedLaplace_repWitness_from_principalParts
#print axioms shiftedLaplace_hBpp_singleton_from_bridge

end
end RHFormalization
