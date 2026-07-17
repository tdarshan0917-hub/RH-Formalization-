import RHFormalization.PrimeSideAlignmentContractLocalEF

/-!
# RHFormalization.PrimeSideOperatorBridgeBLocalEF

Specializes the green Btr/local-EF route to the actual D-side exported
prime object:

  designedY.toOperatorResolventBridge.B

This is not a wrapper around the failed zero-density adapter.  It removes the
abstract `A : PrimeSideAlignmentContract ...` input and states the remaining
E-side payload directly for the actual operator-bridge B-function.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
RH from local explicit-formula data for the actual D-side B-function.

Remaining E-side payload is now concrete:

* `D.B` has the opposite principal parts at witness pole points;
* `D.B` is regular away from witness pole points;
* `D.B + ZpoleSeries` has witness-local holomorphic extensions.

This is the actual wall to attack next.
-/
theorem RH_from_operatorBridgeB_localEF
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (ZF : ZetaZeroFacts)
    (hPP :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          designedY.toOperatorResolventBridge.B
          W.s0
          (-(groupedResidueCoeff
              defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))))
    (hReg :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC
              designedY.toOperatorResolventBridge.B
              z)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ =>
                designedY.toOperatorResolventBridge.B s
                  + ZpoleSeries defaultZeroMultiplicityData s)
              W.s0)
    (hσ :
      0 ≤ designedY.toOperatorResolventBridge.sigma0) :
    RiemannHypothesis :=
  RH_from_primeSideAlignmentContract_localEF
    h_real_zero_free
    convergence
    poleSeriesMeromorphic
    (primeSideAlignmentContract_of_D_B
      defaultZeroMultiplicityData
      designedY.toOperatorResolventBridge
      hPP
      hReg)
    ZF
    h_witness
    hσ

#check RH_from_operatorBridgeB_localEF
#print axioms RH_from_operatorBridgeB_localEF

end

end RHFormalization
