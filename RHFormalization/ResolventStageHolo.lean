import RHFormalization.CorrectedResolventPayload
import RHFormalization.ResolventTraceHolo
import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.HExplicitFormulaHolomorphyLocal
import RHFormalization.PrimePowerDFiniteStage
import Mathlib

/-!
# h_stage_holo for the live resolvent family

`R_stage α = spectralResolventPartial α − finiteCanonical(resolventIndices α) shiftedLaplaceHeatKernelC`
is holomorphic on Ω at every stage. F-part: finite sum of resolvent terms `(s+λₖ)⁻¹`, each analytic
on Ω (λₖ = (k·π)² ≥ 0, so s+λₖ ≠ 0 on Ω). B-part: banked s-dependent prime-package holomorphy.
Combine by `.sub`, lift pointwise→on-Ω. Discharges dcanrem input h_stage_holo for the resolvent layer.
-/

namespace RHFormalization
open Filter Topology Complex Set

/-- The F-part `spectralResolventPartial α` is analytic at each `z ∈ Ω`. -/
theorem spectralResolventPartial_analyticAt (α : DFiniteStage) {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ (spectralResolventPartial α) z := by
  unfold spectralResolventPartial
  have hterm : ∀ k ∈ Finset.range (resolventIndices α).card,
      AnalyticAt ℂ (fun s => (s + ((concreteDirichletPWQOData.lamShifted k : ℝ) : ℂ))⁻¹) z := by
    intro k _
    exact resolvent_term_analyticAt (concreteDirichletPWQOData.lamShifted k)
      (concreteDirichletPWQOData.nonneg k) hz
  exact Finset.analyticAt_fun_sum _ hterm

/-- The F-part `spectralResolventPartial α` is holomorphic on Ω. -/
theorem spectralResolventPartial_holo_on_Omega (α : DFiniteStage) :
    HolomorphicOnC (spectralResolventPartial α) Ω :=
  holomorphicOnC_of_forall_holomorphicAtC _ _
    (fun z hz => spectralResolventPartial_analyticAt α hz)

/-- **h_stage_holo for the resolvent family.** `R_stage α` is holomorphic on Ω at every stage. -/
theorem resolvent_stage_holo (α : DFiniteStage) :
    HolomorphicOnC (fun s => correctedResolventPayload.R_stage α s) Ω := by
  apply holomorphicOnC_of_forall_holomorphicAtC
  intro z hz
  show HolomorphicAtC
    (fun s => spectralResolventPartial α s -
      finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s) z
  have hF : AnalyticAt ℂ (spectralResolventPartial α) z :=
    spectralResolventPartial_analyticAt α hz
  have hB : AnalyticAt ℂ
      (finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC) z :=
    finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
      (resolventIndices α) z hz
  exact hF.sub hB

/-- Specialized to the live primePowerStage net (the exact dcanrem h_stage_holo shape). -/
theorem resolvent_stage_holo_primePowerStage :
    ∀ n : ℕ, HolomorphicOnC
      (fun s => correctedResolventPayload.R_stage (primePowerStage n) s) Ω :=
  fun n => resolvent_stage_holo (primePowerStage n)

#print axioms resolvent_stage_holo
#print axioms resolvent_stage_holo_primePowerStage

end RHFormalization
