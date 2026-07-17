import RHFormalization.CorrectedResolventPayload
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/--
If the corrected spectral F-part and prime B-part are separately compact-uniformly
bounded, then the corrected residual is compact-uniformly bounded.
-/
theorem correctedResolventPayload_R_stage_bound_of_F_B_bounds
    (hF :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∃ CF : ℝ,
            0 ≤ CF ∧
              ∀ α : DFiniteStage,
              ∀ s : ℂ,
                s ∈ K →
                  ‖spectralResolventPartial α s‖ ≤ CF)
    (hB :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∃ CB : ℝ,
            0 ≤ CB ∧
              ∀ α : DFiniteStage,
              ∀ s : ℂ,
                s ∈ K →
                  ‖finiteCanonicalPrimePowerPackage
                      (resolventIndices α)
                      shiftedLaplaceHeatKernelC
                      s‖ ≤ CB) :
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖correctedResolventPayload.R_stage α s‖ ≤ C := by
  intro K hK hKOmega
  obtain ⟨CF, hCF_nonneg, hCF⟩ := hF K hK hKOmega
  obtain ⟨CB, hCB_nonneg, hCB⟩ := hB K hK hKOmega
  refine ⟨CF + CB, add_nonneg hCF_nonneg hCB_nonneg, ?_⟩
  intro α s hs
  unfold correctedResolventPayload spectralResolventPartial
  dsimp
  calc
    ‖(Finset.range (resolventIndices α).card).sum
        (fun k => (s + ↑(concreteDirichletPWQOData.lamShifted k))⁻¹)
        - finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s‖
        ≤ ‖spectralResolventPartial α s‖
          + ‖finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s‖ := by
            simpa [spectralResolventPartial] using
              norm_sub_le
                ((Finset.range (resolventIndices α).card).sum
                  (fun k => (s + ↑(concreteDirichletPWQOData.lamShifted k))⁻¹))
                (finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s)
    _ ≤ CF + CB := by
      exact add_le_add (hCF α s hs) (hCB α s hs)

end
end RHFormalization
