import RHFormalization.ShiftedLaplaceRepZpoleResidue
import RHFormalization.ShiftedLaplaceWitnessCancellation
import RHFormalization.ShiftedLaplaceBppFromBridge

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem shiftedLaplace_repWitness_extension
    (sigma0 : ℝ)
    (hcancel :
      ∀ W : ZeroWitness,
        WitnessCancellationData
          (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          (ZpoleRepSeries defaultZeroMultiplicityData)
          W) :
    ∀ W : ZeroWitness,
      ∃ h : ℂ → ℂ,
        HolomorphicAtC h W.s0 ∧
          LocalEqAtC h
            (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
              + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 := by
  intro W
  exact witness_extension_from_cancellation_data
    (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
    (ZpoleRepSeries defaultZeroMultiplicityData) W (hcancel W)

#print axioms shiftedLaplace_repWitness_extension

end
end RHFormalization
