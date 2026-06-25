import RHFormalization.ResolventDFHLimit
import RHFormalization.ResolventDBcanLimit
import RHFormalization.ArithmeticShiftedLaplaceBStageConvergence
import RHFormalization.CorrectedResolventPayload
import Mathlib

/-!
# h_overlap input for the resolvent bridge

Assembles pointwise R_stage convergence on RightHalfPlane 1 from two banked limits:
F-side resolvent_F_stage_to_FH -> resolventFH, B-side
shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1 -> Bshared.
R_stage = F_stage - B_stage, so Tendsto.sub gives R_stage -> resolventFH - Bshared.
Index alignment is definitional: resolventIndices (primePowerStage n)
= concretePrimePowerBelowCutoff ((n:R)+1) by rfl.
-/

namespace RHFormalization
open Filter Topology Complex

/-- The canonical residual limit: R_H = resolventFH - Bshared. -/
noncomputable def resolventRH : ℂ → ℂ :=
  fun s => resolventFH s - (shiftedLaplaceModelPackageAt 1).Bshared s

/-- h_overlap (live resolvent layer). -/
theorem resolvent_R_stage_overlap_tendsto
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        spectralResolventPartial (primePowerStage n) s -
          finiteCanonicalPrimePowerPackage
            (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
      atTop (nhds (resolventRH s)) := by
  have hsΩ : s ∈ Ω := rightHalfPlane_subset_Omega 1 (by norm_num) hs
  have hF : Tendsto
      (fun n : ℕ => spectralResolventPartial (primePowerStage n) s)
      atTop (nhds (resolventFH s)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := resolvent_F_stage_to_FH ({s} : Set ℂ) isCompact_singleton
      (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; exact hsΩ) ε hε
    exact h.mono (fun n hn => hn s (Set.mem_singleton s))
  have hB : Tendsto
      (fun n : ℕ =>
        finiteCanonicalPrimePowerPackage
          (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
      atTop (nhds ((shiftedLaplaceModelPackageAt 1).Bshared s)) :=
    shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1 s hs
  simpa [resolventRH] using hF.sub hB

#print axioms resolvent_R_stage_overlap_tendsto

end RHFormalization
