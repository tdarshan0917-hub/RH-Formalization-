import RHFormalization.PrimeDUSRToMontelTarget
import RHFormalization.PrimePerturbedPayloadAligned
import RHFormalization.HalfPlaneGeometry
import Mathlib

/-!
# Aligned prime overlap from F-side and B-side convergence (the Tendsto.sub bridge).

The aligned R_stage = F_stage - B_stage with
  F_stage = primePerturbedFStage mu (...),  B_stage = arithmeticShiftedLaplaceBStage.
Given F_stage -> F_H and B_stage -> B_H pointwise on RightHalfPlane 1 (subset of Omega),
Tendsto.sub gives R_stage -> F_H - B_H on the overlap. This is the algebraic bridge only:
the F-side convergence is the named analytic premise (manuscript h_F_stage_to_FH for the
prime operator); the B-side is the banked arithmeticPrime...tendsto_Bshared_sigma1.

NOT a certificate: the overlap is DERIVED by Tendsto.sub; the convergences are the premises.
-/

namespace RHFormalization
noncomputable section
open Filter Topology Complex

variable {N : ℕ}

/-- **Aligned overlap from F and B convergence.** -/
theorem primePerturbedAlignedOverlap_from_F_and_B
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (F_H B_H : ℂ → ℂ)
    (h_F_to_FH : ∀ s ∈ RightHalfPlane (1 : ℝ),
        Tendsto (fun n => primePerturbedFStage μ
          (primeStageWeights (primePerturbedStageIndex (alpha n))) s)
          atTop (nhds (F_H s)))
    (h_B_to_BH : ∀ s ∈ RightHalfPlane (1 : ℝ),
        Tendsto (fun n => arithmeticShiftedLaplaceBStage (alpha n) s)
          atTop (nhds (B_H s))) :
    PrimePerturbedAlignedOverlap μ alpha (fun s => F_H s - B_H s) := by
  refine ⟨RightHalfPlane 1, isOpen_RightHalfPlane 1, rightHalfPlane_nonempty 1,
    rightHalfPlane_subset_Omega 1 (by norm_num), ?_⟩
  intro s hs
  have hF := h_F_to_FH s hs
  have hB := h_B_to_BH s hs
  -- R_stage (alpha n) s = F_stage - B_stage definitionally
  have hsub := hF.sub hB
  -- the aligned R_stage is exactly primePerturbedFStage ... - arithmeticShiftedLaplaceBStage ...
  simpa using hsub

#print axioms primePerturbedAlignedOverlap_from_F_and_B

end
end RHFormalization
