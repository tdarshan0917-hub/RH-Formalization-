import RHFormalization.ArithmeticShiftedLaplaceBStageConcrete
import RHFormalization.ShiftedLaplaceModelExhaustionSigma1

/-!
# ArithmeticShiftedLaplaceBStageConvergence

Clean arithmetic shifted-Laplace B-stage convergence.

This proves the concrete finite cutoff convergence directly, then transfers it
to the clean arithmetic B-stage using the concrete connector.

Critical fix:
  the eventual-coverage filter variable is explicitly `n : ℕ`.

No designedSpikeWitness in the final arithmetic statement.
No stageFieldSpikeExtractionWitness.
No displacement kernel.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators Classical

/--
Concrete shifted-Laplace finite canonical packages over

  concretePrimePowerBelowCutoff ((n : ℝ) + 1)

converge pointwise on `RightHalfPlane 1` to the shifted-Laplace model package.
-/
theorem shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1
    (s : ℂ)
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        finiteCanonicalPrimePowerPackage
          (concretePrimePowerBelowCutoff ((n : ℝ) + 1))
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
          q ∈ concretePrimePowerBelowCutoff ((n : ℝ) + 1) := by
    intro q hqne

    have hvalid : IsPrimePowerPair q := by
      by_contra hbad
      apply hqne
      have hw0 : q.weightReal = 0 := by
        simp [PrimePowerPair.weightReal, hbad]
      simp [PrimePowerPair.weightC, hw0]

    have hev :
        ∀ᶠ n : ℕ in atTop,
          q.center ≤ (n : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop ⌈q.center⌉₊] with n hn
      have hceil : q.center ≤ (⌈q.center⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hcast : ((⌈q.center⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      linarith

    filter_upwards [hev] with n hn
    exact concretePrimePowerEnum.h_mem_belowCutoff
      ((n : ℝ) + 1) q hvalid hn

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

/--
The clean arithmetic shifted-Laplace B-stage sequence is pointwise equal to the
concrete finite canonical package sequence.
-/
theorem arithmeticPrimeShiftedLaplaceBStage_seq_eq_concrete
    {N : ℕ}
    (μ : ℕ → Fin N → ℝ)
    (M : ℕ → ℝ)
    (hnn :
      ∀ n : ℕ,
        ∀ y : EuclideanSpace ℂ (Fin N),
          0 ≤ RCLike.re
            (inner ℂ y
              (primeOpCLM (μ n) (primeStageWeights (N := N) n) (M n) y)))
    (s : ℂ) :
    (fun n : ℕ =>
      arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n (μ n) (M n) (hnn n)) s)
      =
    (fun n : ℕ =>
      finiteCanonicalPrimePowerPackage
        (concretePrimePowerBelowCutoff ((n : ℝ) + 1))
        shiftedLaplaceHeatKernelC
        s) := by
  funext n
  exact
    arithmeticPrimeShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_concrete
      n (μ n) (M n) (hnn n) s

/--
The clean arithmetic shifted-Laplace finite B-stages converge pointwise on
`RightHalfPlane 1` to the shifted-Laplace model/shared package.

The μ/M/hnn inputs may vary with n; they do not affect the finite prime-power
B-stage after the clean concrete-index identification.
-/
theorem arithmeticPrimeShiftedLaplaceBStage_tendsto_Bshared_sigma1
    {N : ℕ}
    (μ : ℕ → Fin N → ℝ)
    (M : ℕ → ℝ)
    (hnn :
      ∀ n : ℕ,
        ∀ y : EuclideanSpace ℂ (Fin N),
          0 ≤ RCLike.re
            (inner ℂ y
              (primeOpCLM (μ n) (primeStageWeights (N := N) n) (M n) y)))
    (s : ℂ)
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        arithmeticShiftedLaplaceBStage
          (arithmeticPrimeOperatorDFiniteStage n (μ n) (M n) (hnn n)) s)
      Filter.atTop
      (𝓝 ((shiftedLaplaceModelPackageAt 1).Bshared s)) := by
  have hseq :=
    arithmeticPrimeShiftedLaplaceBStage_seq_eq_concrete μ M hnn s
  rw [hseq]
  exact shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1 s hs

#print axioms shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1
#print axioms arithmeticPrimeShiftedLaplaceBStage_seq_eq_concrete
#print axioms arithmeticPrimeShiftedLaplaceBStage_tendsto_Bshared_sigma1

end

end RHFormalization
