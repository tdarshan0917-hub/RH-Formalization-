import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.PrimePerturbedFStage
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.CorrectedResolventPayload
import Mathlib

/-!
# Prime-perturbed operator payload (the RIGHT F-object)

Mirrors `correctedResolventPayload` but with F_stage = the genuine prime-perturbed
operator `primePerturbedFStage μ (primeStageWeights n)`, NOT the free spectrum
`spectralResolventPartial` (lamShifted = (nπ)²).

Same B_stage (shifted-Laplace finite canonical), same sigma0, R = F - B.
-/

namespace RHFormalization
open Complex Set

/-- Map a DFiniteStage to its ℕ cutoff index (same convention as the free layer). -/
noncomputable def primePerturbedStageIndex (α : DFiniteStage) : ℕ :=
  (resolventIndices α).card

/-- **Prime-perturbed payload.** F = real prime operator; B = shifted-Laplace canonical. -/
noncomputable def primePerturbedPayload (μ : Fin N → ℝ) : SelectedFiniteCanonicalPayload :=
{ F_stage := fun α s =>
    primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s
  B_stage := fun α s =>
    finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s
  R_stage := fun α s =>
    primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s -
      finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s
  sigma0 := 1
  h_stage_split := by intro α s hs; ring
  indices := resolventIndices
  kernel := fun _ => shiftedLaplaceHeatKernelC
  h_B_stage_eq_finiteCanonical := by intro α s; rfl }

#print axioms primePerturbedPayload

end RHFormalization
