import RHFormalization.ShiftedLaplaceRepSumOrder
import RHFormalization.PrincipalPartMeromorphic
import RHFormalization.ShiftedLaplaceHoloLocalReduction
import Mathlib.Analysis.Meromorphic.Order

namespace RHFormalization
noncomputable section
open Complex Filter Topology

/-- The corrected prime+pole function at one witness: equals `Bshared + ZpoleRep`
away from the witness, and takes the removable-limit value at the witness. -/
noncomputable def repSumCorrectedAt
    (sigma0 : ℝ) (W : ZeroWitness) (c : ℂ) : ℂ → ℂ :=
  Function.update
    (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
      + ZpoleRepSeries defaultZeroMultiplicityData s)
    W.s0 c

/-- Witness-extension data via meromorphic order. From the opposite principal parts,
`Bshared + ZpoleRep` is meromorphic with nonnegative order at the witness, hence has a
limit; the function updated to that limit at the witness is analytic there and agrees
with the raw sum on the punctured neighborhood. The center value is exactly the
removable limit `limUnder`. Replaces the false `hpoint`. -/
theorem repWitness_extension_via_order
    (sigma0 : ℝ) (W : ZeroWitness)
    (hBpp : HasPrincipalPartAtC
      (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
      W.s0 ((zetaZeroMult W.ρ : ℂ))) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h W.s0 ∧
        (∀ᶠ w in 𝓝[≠] W.s0,
          h w = (shiftedLaplacePrimePackageAt sigma0).Bshared w
            + ZpoleRepSeries defaultZeroMultiplicityData w) ∧
        h W.s0 = limUnder (𝓝[≠] W.s0)
          (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleRepSeries defaultZeroMultiplicityData s) := by
  classical
  have hMerB : MeromorphicAt
      (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s) W.s0 :=
    hasPrincipalPartAtC_meromorphicAt _ W.s0 _ hBpp
  have hMerZ : MeromorphicAt (ZpoleRepSeries defaultZeroMultiplicityData) W.s0 :=
    hasPrincipalPartAtC_meromorphicAt _ W.s0 _ hZpp_rep
  have hMer : MeromorphicAt
      (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
        + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 :=
    hMerB.add hMerZ
  have hOrd := repSum_meromorphicOrderAt_nonneg sigma0 W hBpp hZpp_rep
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hMer hOrd
  have hlim : limUnder (𝓝[≠] W.s0)
      (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
        + ZpoleRepSeries defaultZeroMultiplicityData s) = c := hc.limUnder_eq
  have hpunct : (∀ᶠ w in 𝓝[≠] W.s0,
      repSumCorrectedAt sigma0 W c w
        = (shiftedLaplacePrimePackageAt sigma0).Bshared w
          + ZpoleRepSeries defaultZeroMultiplicityData w) := by
    filter_upwards [self_mem_nhdsWithin] with w hwne
    have hne : w ≠ W.s0 := hwne
    simp only [repSumCorrectedAt, Function.update_of_ne hne]
  refine ⟨repSumCorrectedAt sigma0 W c, ?_, hpunct, ?_⟩
  · have hMerU : MeromorphicAt (repSumCorrectedAt sigma0 W c) W.s0 :=
      hMer.congr (Filter.EventuallyEq.symm hpunct)
    have hCont : ContinuousAt (repSumCorrectedAt sigma0 W c) W.s0 := by
      have hval : repSumCorrectedAt sigma0 W c W.s0 = c := by
        simp [repSumCorrectedAt]
      rw [continuousAt_iff_punctured_nhds, hval]
      refine hc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hwne
      have hne : w ≠ W.s0 := hwne
      simp only [repSumCorrectedAt, Function.update_of_ne hne]
    exact hMerU.analyticAt hCont
  · -- h W.s0 = c = limUnder
    have hval : repSumCorrectedAt sigma0 W c W.s0 = c := by
      simp [repSumCorrectedAt]
    rw [hval, hlim]

#print axioms repWitness_extension_via_order

end
end RHFormalization
