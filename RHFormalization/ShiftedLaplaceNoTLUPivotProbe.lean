import RHFormalization.ShiftedLaplaceUnconditional
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceBppFromBridge
import RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts
import RHFormalization.ShiftedLaplaceRegularFromZeroDensity

namespace RHFormalization
noncomputable section

open Complex Set Topology Filter

/--
Pivot probe:

Can we get shifted-Laplace H-holomorphy from meromorphic continuation
and principal-part cancellation WITHOUT global Ω TLU?

Expected remaining target:
  hB_regular away from witnesses.
-/
theorem shiftedLaplace_no_tlu_holo_pivot_probe
    (sigma0 : ℝ)
    (hBmero :
      MeromorphicOnC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Ω)
    (hVopen : IsOpen shiftedLaplaceAbsConvRegion)
    (hVne : shiftedLaplaceAbsConvRegion.Nonempty)
    (hVsub : shiftedLaplaceAbsConvRegion ⊆ Ω)
    (hZpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (ZpoleSeries defaultZeroMultiplicityData)
          W.s0
          (groupedResidueCoeff
            defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W)))
    (hpoint :
      ∀ W : ZeroWitness,
        Classical.choose
            (shiftedLaplace_hBpp_from_bridge
              sigma0
              (shiftedLaplace_bridge_from_meromorphy
                sigma0 hBmero hVopen hVne hVsub)
              W)
            W.s0
          +
        Classical.choose
            (hZpp W)
            W.s0
        =
        (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0
          + ZpoleSeries defaultZeroMultiplicityData W.s0)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts) :
    HolomorphicOnC (shiftedLaplaceAppendixHFunction sigma0) Ω := by

  have hbridge :
      ShiftedLaplaceBridgeData sigma0 :=
    shiftedLaplace_bridge_from_meromorphy
      sigma0 hBmero hVopen hVne hVsub

  have hBpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          W.s0
          (-groupedResidueCoeff
            defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W)) :=
    shiftedLaplace_hBpp_from_bridge sigma0 hbridge

  have hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W :=
    shiftedLaplace_hcancel_from_grouped_principalParts
      sigma0
      (fun W => defaultGroupedPoleClass defaultZeroMultiplicityData W)
      hBpp
      hZpp
      hpoint

  refine
    shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity
      sigma0
      hsum
      ZF
      hcancel
      ?_

  /-
  This is the true pivot target.
  If Lean stops here, we know exactly what must be proved next:
  Bshared is holomorphic away from the witness poles, derived from hBmero
  plus a "no extra poles" theorem.
  -/
  trace_state
  fail

end
end RHFormalization
