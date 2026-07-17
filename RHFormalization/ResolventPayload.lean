import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.SelectedFiniteStageOperatorLegality
import RHFormalization.CanonicalPrimePowerPackage

namespace RHFormalization
noncomputable section
open Complex

noncomputable def resolventKernel : CanonicalKernelC :=
  fun a s => (s + ((a : ℂ)))⁻¹

/-- Indices per stage: empty for now (placeholder finite set); the resolvent
    content lives in the kernel. Swapped to the real eigenvalue index next. -/
noncomputable def resolventIndices : DFiniteStage → Finset PrimePowerPair :=
  fun _ => ∅

noncomputable def resolventPayload : SelectedFiniteCanonicalPayload :=
{ F_stage := fun α s =>
    finiteCanonicalPrimePowerPackage (resolventIndices α) resolventKernel s
  B_stage := fun α s =>
    finiteCanonicalPrimePowerPackage (resolventIndices α) resolventKernel s
  R_stage := fun _ _ => 0
  sigma0 := 0
  h_stage_split := by intro α s hs; simp
  indices := resolventIndices
  kernel := fun _ => resolventKernel
  h_B_stage_eq_finiteCanonical := by intro α s; rfl }

#print axioms resolventPayload

end
end RHFormalization
