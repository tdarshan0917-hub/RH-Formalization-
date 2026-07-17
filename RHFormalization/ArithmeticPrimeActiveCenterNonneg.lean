import RHFormalization.ArithmeticShiftedPrimeDExportAbsConvBall

/-!
# ArithmeticPrimeActiveCenterNonneg

Removes the active-center nonnegativity hypothesis.

This is finite/combinatorial:
valid prime-power pair ⇒ p^m ≥ 1 ⇒ log(p^m) ≥ 0.
-/

namespace RHFormalization

noncomputable section

open Complex Metric
open scoped BigOperators Classical

/-- A valid prime-power pair has nonnegative logarithmic center. -/
theorem primePowerPair_center_nonneg_of_valid
    (q : PrimePowerPair)
    (hq : IsPrimePowerPair q) :
    0 ≤ PrimePowerPair.center q := by
  have hp2 : 2 ≤ q.p := hq.1.two_le
  have hp_pos : 0 < q.p := by
    exact lt_of_lt_of_le (by norm_num) hp2
  have hnatpos : 0 < q.natValue := by
    unfold PrimePowerPair.natValue
    exact Nat.pow_pos hp_pos
  have hnat : (1 : ℕ) ≤ q.natValue :=
    Nat.succ_le_of_lt hnatpos
  have hreal : (1 : ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa [PrimePowerPair.center] using Real.log_nonneg hreal

/-- Active pp-stage codes decode to valid prime powers, hence have nonnegative centers. -/
theorem ppStageCodes_center_nonneg
    {n k : ℕ}
    (hk : k ∈ ppStageCodes n) :
    0 ≤ PrimePowerPair.center (ppDecode k) := by
  rcases mem_ppStageCodes.mp hk with ⟨q, hqmem, hcode⟩
  have hfil := Finset.mem_filter.mp hqmem
  have hvalid : IsPrimePowerPair q := hfil.2.1
  have hdecode : ppDecode k = q := by
    rw [← hcode]
    exact ppDecode_ppCode q
  simpa [hdecode] using primePowerPair_center_nonneg_of_valid q hvalid

/--
The arithmetic prime-operator DFiniteStage inherits its active spike codes from
`primePowerStage`; therefore all active centers are nonnegative.
-/
theorem arithmeticPrimeOperatorDFiniteStage_active_center_nonneg
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y))) :
    ∀ q ∈ (arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeActiveIndices,
      0 ≤ PrimePowerPair.center
        ((arithmeticPrimeOperatorDFiniteStage n μ M hnn).diagonalSpikeToPP q) := by
  intro q hq
  simpa [arithmeticPrimeOperatorDFiniteStage, primeOperatorDFiniteStage, primePowerStage]
    using ppStageCodes_center_nonneg (n := n) (k := q) hq

/--
Corrected finite-stage D.EXPORT on a shifted-Laplace absolute-convergence ball,
with active-center nonnegativity discharged.

Remaining local assumption:
* the global shift is large enough in the Weyl/growthDrop/free-spectrum sense.
-/
theorem ArithmeticShiftedPrimeDExport_on_absConv_closedBall_noCenter
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y)))
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hVball : Metric.closedBall c r ⊆ shiftedLaplaceAbsConvRegion)
    (hfree :
      ∀ i : Fin N,
        growthDrop (primePotential (primeStageWeights (N := N) n))
          ≤ freeEigenvalues (μShift μ M) i) :
    PerturbedDExport
      (μShift μ M)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ M hnn))
      (Metric.closedBall c r) := by
  exact ArithmeticShiftedPrimeDExport_on_absConv_closedBall_shiftedLaplaceBStage
    n μ M hnn
    c r hr
    hVball
    hfree
    (arithmeticPrimeOperatorDFiniteStage_active_center_nonneg n μ M hnn)

#print axioms primePowerPair_center_nonneg_of_valid
#print axioms ppStageCodes_center_nonneg
#print axioms arithmeticPrimeOperatorDFiniteStage_active_center_nonneg
#print axioms ArithmeticShiftedPrimeDExport_on_absConv_closedBall_noCenter

end

end RHFormalization
