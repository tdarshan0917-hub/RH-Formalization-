import RHFormalization.PrimeSideAlignmentContract
import RHFormalization.PrimeSideOverlapAlignmentLocalEF

/-!
# RHFormalization.PrimeSideAlignmentContractLocalEF

Bridge from the stronger prime-side alignment contract to the green local-EF
overlap route.

This is not a new capstone. It compresses the current E-side route:

* `PrimeSideAlignmentContract` already contains overlap alignment;
* it also contains regularity of `Btr` away from witness poles;
* therefore the only remaining local-EF input is the witness-local extension
  of `Btr + ZpoleSeries`.

The old displacement-kernel branch is not used.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
Forget the extra principal-part and regularity fields of
`PrimeSideAlignmentContract`, keeping only the overlap alignment needed by
`PrimeSideOverlapAlignment`.
-/
def overlapAlignment_of_primeSideAlignmentContract
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideAlignmentContract M D) :
    PrimeSideOverlapAlignment D :=
  { Btr := A.Btr
    h_Btr_matches_D_on_overlap :=
      A.h_Btr_matches_D_on_overlap }

/--
RH through the corrected prime-side alignment contract and local EF.

Compared with `RH_from_primeSideOverlapAlignment_localEF`, this theorem no
longer asks separately for regularity of `Btr` away from witnesses; it obtains
that regularity from the strong alignment contract.

Remaining E-side local input:

  local witness extensions of `A.Btr + ZpoleSeries`.
-/
theorem RH_from_primeSideAlignmentContract_localEF
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
    (A :
      PrimeSideAlignmentContract
        defaultZeroMultiplicityData
        designedY.toOperatorResolventBridge)
    (ZF : ZetaZeroFacts)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ =>
                A.Btr s + ZpoleSeries defaultZeroMultiplicityData s)
              W.s0)
    (hσ :
      0 ≤ designedY.toOperatorResolventBridge.sigma0) :
    RiemannHypothesis :=
  RH_from_primeSideOverlapAlignment_localEF
    h_real_zero_free
    convergence
    poleSeriesMeromorphic
    (overlapAlignment_of_primeSideAlignmentContract
      defaultZeroMultiplicityData
      designedY.toOperatorResolventBridge
      A)
    ZF
    h_witness
    (by
      intro z hzΩ hnotW
      exact A.h_Btr_regular_away_from_witnesses z hzΩ hnotW)
    hσ

#check overlapAlignment_of_primeSideAlignmentContract
#check RH_from_primeSideAlignmentContract_localEF
#print axioms RH_from_primeSideAlignmentContract_localEF

end

end RHFormalization
