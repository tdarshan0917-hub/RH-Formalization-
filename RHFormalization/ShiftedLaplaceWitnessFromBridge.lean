import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceBppFromBridge
import RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts
import RHFormalization.ShiftedLaplaceWitnessCancellation

namespace RHFormalization

noncomputable section

open Complex Filter Topology

theorem shiftedLaplace_h_witness_from_bridge
    (sigma0 : ℝ)
    (hBmero :
      MeromorphicOnC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s) Ω)
    (hVopen : IsOpen shiftedLaplaceAbsConvRegion)
    (hVne : shiftedLaplaceAbsConvRegion.Nonempty)
    (hVsub : shiftedLaplaceAbsConvRegion ⊆ Ω)
    (hZpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (ZpoleSeries defaultZeroMultiplicityData)
          W.s0
          (groupedResidueCoeff defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W)))
    (hpoint :
      ∀ W : ZeroWitness,
        (Classical.choose
          (shiftedLaplace_hBpp_from_bridge sigma0
            (shiftedLaplace_bridge_from_meromorphy sigma0 hBmero hVopen hVne hVsub) W)) W.s0 +
          (Classical.choose (hZpp W)) W.s0 =
            (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0 +
              ZpoleSeries defaultZeroMultiplicityData W.s0) :
    ∀ W : ZeroWitness,
      ∃ h : ℂ → ℂ,
        HolomorphicAtC h W.s0 ∧
          LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) W.s0 := by
  apply shiftedLaplace_witness_extensions_from_cancellation_data sigma0
  exact
    shiftedLaplace_hcancel_from_grouped_principalParts sigma0
      (fun W => defaultGroupedPoleClass defaultZeroMultiplicityData W)
      (shiftedLaplace_hBpp_from_bridge sigma0
        (shiftedLaplace_bridge_from_meromorphy sigma0 hBmero hVopen hVne hVsub))
      hZpp hpoint

#print axioms shiftedLaplace_h_witness_from_bridge

end

end RHFormalization
