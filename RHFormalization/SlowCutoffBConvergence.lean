import RHFormalization.ArithmeticShiftedLaplaceBStageConvergence

/-!
# RHFormalization.SlowCutoffBConvergence

**Phase 2a of the schedule retune.** The sigma=1 B-convergence engine,
generalized from the hardwired cutoff `(n:ℝ)+1` to ANY cutoff `c → ∞`.
Textual transform of the banked donor
`shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1`; the schedule
enters only through the coverage step, discharged by
`hc.eventually_ge_atTop`. Schedule-independent — banks before the `admR` flip.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators Classical

/--
Concrete shifted-Laplace finite canonical packages over
`concretePrimePowerBelowCutoff (c n)` converge pointwise on `RightHalfPlane 1`
to the shifted-Laplace model package, for ANY cutoff `c → ∞`.
-/
theorem shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1_along
    (c : ℕ → ℝ) (hc : Filter.Tendsto c Filter.atTop Filter.atTop)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        finiteCanonicalPrimePowerPackage
          (concretePrimePowerBelowCutoff (c n))
          shiftedLaplaceHeatKernelC
          s)
      Filter.atTop
      (𝓝 ((shiftedLaplaceModelPackageAt 1).Bshared s)) := by
  have hsabs : s ∈ shiftedLaplaceAbsConvRegion :=
    rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion hs
  have hsumm :
      Summable
        (fun q : PrimePowerPair =>
          q.weightC * shiftedLaplaceHeatKernelC q.center s) :=
    shiftedLaplace_family_summable hsabs
  have hcover :
      ∀ q : PrimePowerPair,
        (q.weightC * shiftedLaplaceHeatKernelC q.center s) ≠ 0 →
        ∀ᶠ n : ℕ in atTop,
          q ∈ concretePrimePowerBelowCutoff (c n) := by
    intro q hqne
    have hvalid : IsPrimePowerPair q := by
      by_contra hbad
      apply hqne
      have hw0 : q.weightReal = 0 := by
        simp [PrimePowerPair.weightReal, hbad]
      simp [PrimePowerPair.weightC, hw0]
    have hev : ∀ᶠ n : ℕ in atTop, q.center ≤ c n :=
      hc.eventually_ge_atTop q.center
    filter_upwards [hev] with n hn
    exact concretePrimePowerEnum.h_mem_belowCutoff (c n) q hvalid hn
  have hconv :=
    tendsto_sum_of_eventually_covers_support hsumm hcover
  have htsum_model :
      (∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center s)
        =
      (shiftedLaplaceModelPackageAt 1).Bshared s := by
    rw [← shiftedLaplacePrimePackageAt_Bshared_eq_tsum 1 s]
    show (shiftedLaplacePrimePackageAt 1).Bshared s =
      shiftedLaplaceLogDerivModel s
    exact shiftedLaplace_Bshared_eqOn_model 1 hsabs
  rw [← htsum_model]
  simpa [finiteCanonicalPrimePowerPackage] using hconv

#print axioms shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1_along

end

end RHFormalization
