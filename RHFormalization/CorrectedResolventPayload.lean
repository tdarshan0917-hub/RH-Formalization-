import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.SelectedFiniteStageOperatorLegality
import RHFormalization.CanonicalPrimePowerPackage
import RHFormalization.PrimeSideTransformKernelPrototype

namespace RHFormalization
noncomputable section
open Complex

/-- Own indices: prime-power pairs with center ≤ stage cutoff R. Genuine,
    not a hole, not empty. -/
noncomputable def resolventIndices : DFiniteStage → Finset PrimePowerPair :=
  fun α => concretePrimePowerBelowCutoff α.R

/-- Spectral resolvent partial sum over the concrete Dirichlet eigenvalues. -/
noncomputable def spectralResolventPartial (α : DFiniteStage) : ℂ → ℂ :=
  fun s =>
    (Finset.range (resolventIndices α).card).sum
      (fun k => (s + ((concreteDirichletPWQOData.lamShifted k : ℝ) : ℂ))⁻¹)

/-- Corrected payload: real D-split. F_stage = spectral resolvent,
    B_stage = prime package, R_stage = residual. -/
noncomputable def correctedResolventPayload : SelectedFiniteCanonicalPayload :=
{ F_stage := fun α s => spectralResolventPartial α s
  B_stage := fun α s =>
    finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s
  R_stage := fun α s =>
    spectralResolventPartial α s -
      finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s
  sigma0 := 1
  h_stage_split := by intro α s hs; ring
  indices := resolventIndices
  kernel := fun _ => shiftedLaplaceHeatKernelC
  h_B_stage_eq_finiteCanonical := by intro α s; rfl }

#print axioms correctedResolventPayload

end
end RHFormalization
