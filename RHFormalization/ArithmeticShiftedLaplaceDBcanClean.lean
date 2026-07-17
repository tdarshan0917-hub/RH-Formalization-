import RHFormalization.ArithmeticShiftedLaplaceBStageConvergence
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.AppendixDPrimePowerLimitReduction

/-!
# ArithmeticShiftedLaplaceDBcanClean

Robust clean DBcan package for the shifted-Laplace arithmetic route.

This file deliberately avoids the fragile constructor path through
`toFiniteCanonicalPrimePowerFormula.indices/kernel`, which previously introduced
`sorryAx`.

What is proved here:

1. A clean finite operator layer at σ = 1 whose B-stage is the clean arithmetic
   shifted-Laplace B-stage.

2. A direct clean `DBcanLimitData` with
      Bcan := (shiftedLaplaceModelPackageAt 1).Bshared.

3. A separate convergence theorem:
      clean arithmetic finite B_stage(n) → this Bcan.

This keeps the mathematical bridge honest without forcing Lean through the
old selected-builder normalization route.

No stageFieldSpikeExtractionWitness.
No displacement kernel.
No sorry.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators Classical

/-- Clean B-side finite-stage transform. -/
noncomputable def arithmeticShiftedLaplaceCleanFStage :
    DFiniteStage → ℂ → ℂ :=
  arithmeticShiftedLaplaceBStage

/-- Clean B-side finite-stage B-part. -/
noncomputable def arithmeticShiftedLaplaceCleanBStage :
    DFiniteStage → ℂ → ℂ :=
  arithmeticShiftedLaplaceBStage

/-- Zero residual for the clean B-side limit package. -/
noncomputable def arithmeticShiftedLaplaceCleanRStage :
    DFiniteStage → ℂ → ℂ :=
  fun _ _ => 0

/-- Stage split at σ = 1 for the clean B-side package. -/
theorem arithmeticShiftedLaplaceClean_stage_split_sigma1 :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane (1 : ℝ),
      arithmeticShiftedLaplaceCleanFStage α s =
        arithmeticShiftedLaplaceCleanBStage α s +
          arithmeticShiftedLaplaceCleanRStage α s := by
  intro α s hs
  simp [
    arithmeticShiftedLaplaceCleanFStage,
    arithmeticShiftedLaplaceCleanBStage,
    arithmeticShiftedLaplaceCleanRStage
  ]

/-- The clean B-stage is the finite Nat spike package from the real stage fields. -/
theorem arithmeticShiftedLaplaceClean_B_stage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      arithmeticShiftedLaplaceCleanBStage α s =
        finiteNatSpikePackage
          α.diagonalSpikeActiveIndices
          α.diagonalSpikeContribution
          (arithmeticShiftedLaplaceSpikeKernel α)
          s := by
  intro α s
  simpa [arithmeticShiftedLaplaceCleanBStage] using
    arithmeticShiftedLaplaceBStage_eq_finiteNatSpikePackage α s

/-- Kernel bridge for the clean shifted-Laplace spike kernel. -/
theorem arithmeticShiftedLaplaceClean_kernel_bridge :
    ∀ (α : DFiniteStage), ∀ n ∈ α.diagonalSpikeActiveIndices, ∀ (s : ℂ),
      arithmeticShiftedLaplaceSpikeKernel α n s =
        shiftedLaplaceHeatKernelC
          (PrimePowerPair.center (α.diagonalSpikeToPP n))
          s := by
  intro α n hn s
  rfl

/--
Clean selected trace/spike payload at σ = 1.

This is built directly from the `DFiniteStage` diagonal spike fields.
-/
noncomputable def arithmeticShiftedLaplaceTraceSpikePayloadSigma1 :
    SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    arithmeticShiftedLaplaceCleanFStage
    arithmeticShiftedLaplaceCleanBStage
    arithmeticShiftedLaplaceCleanRStage
    (1 : ℝ)
    arithmeticShiftedLaplaceClean_stage_split_sigma1
    (fun α => α.diagonalSpikeActiveIndices)
    (fun α => arithmeticShiftedLaplaceSpikeKernel α)
    (by
      intro α q hq
      exact α.h_diagonalSpikeActiveIndices_active q hq)
    arithmeticShiftedLaplaceClean_B_stage_eq_diagonal_sum
    (fun α => α.diagonalSpikeToPP)
    (fun _ => shiftedLaplaceHeatKernelC)
    (by
      intro α m hm n hn hmn
      exact α.h_diagonalSpikeToPP_inj m hm n hn hmn)
    (by
      intro α n hn
      exact α.h_canonicalSpikeContribution_eq_weightC n hn)
    arithmeticShiftedLaplaceClean_kernel_bridge

/--
Clean shifted-Laplace finite operator layer at σ = 1.

This is a B-side layer whose B-stage is the clean shifted-Laplace arithmetic
B-stage.
-/
noncomputable def arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1 :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromTraceSpikePayload
    arithmeticShiftedLaplaceTraceSpikePayloadSigma1

/--
Direct clean DBcan limit data.

We intentionally define `Bcan` as the shared shifted-Laplace package function
and keep the already-proved arithmetic finite-stage convergence as a separate
theorem below. This avoids the previous fragile selected-builder normalization.
-/
noncomputable def arithmeticShiftedLaplaceCleanDBcanLimitSigma1 :
    DBcanLimitData
      arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage :=
  { Bcan := (shiftedLaplaceModelPackageAt 1).Bshared
    Cshared := shiftedLaplaceModelPackageAt 1
    h_Cshared_sigma_le := by
      show (shiftedLaplaceModelPackageAt 1).sigma0 ≤
        arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage.sigma0
      have h1 : (shiftedLaplaceModelPackageAt 1).sigma0 = 1 := rfl
      have h2 :
          arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage.sigma0
            = 1 := rfl
      rw [h1, h2]
    h_Bcan_matches_shared := by
      intro s hs
      rfl }

/-- The clean DBcan function is the shifted-Laplace Bshared function. -/
theorem arithmeticShiftedLaplaceCleanDBcanLimitSigma1_Bcan_eq_Bshared
    (s : ℂ) :
    arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Bcan s =
      (shiftedLaplaceModelPackageAt 1).Bshared s := by
  rfl

/--
The clean arithmetic finite B-stages converge to the clean DBcan function.

This is the actual bridge from the green arithmetic convergence theorem to the
DBcan object.
-/
theorem arithmeticPrimeShiftedLaplaceBStage_tendsto_cleanDBcan_sigma1
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
      (𝓝 (arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Bcan s)) := by
  simpa [arithmeticShiftedLaplaceCleanDBcanLimitSigma1] using
    arithmeticPrimeShiftedLaplaceBStage_tendsto_Bshared_sigma1
      μ M hnn s hs

/-- The clean DBcan object satisfies the package overlap matching field. -/
theorem arithmeticShiftedLaplaceCleanDBcanLimitSigma1_h_Bcan_matches_shared
    (s : ℂ)
    (hs :
      s ∈ RightHalfPlane
        arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage.sigma0) :
    arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Bcan s =
      arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Cshared.Bshared s := by
  exact arithmeticShiftedLaplaceCleanDBcanLimitSigma1.h_Bcan_matches_shared s hs

#print axioms arithmeticShiftedLaplaceTraceSpikePayloadSigma1
#print axioms arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1
#print axioms arithmeticShiftedLaplaceCleanDBcanLimitSigma1
#print axioms arithmeticShiftedLaplaceCleanDBcanLimitSigma1_Bcan_eq_Bshared
#print axioms arithmeticPrimeShiftedLaplaceBStage_tendsto_cleanDBcan_sigma1
#print axioms arithmeticShiftedLaplaceCleanDBcanLimitSigma1_h_Bcan_matches_shared

end

end RHFormalization
