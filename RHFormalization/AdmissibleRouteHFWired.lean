import RHFormalization.AdmissibleRouteHBWired
import RHFormalization.AdmissibleDFHLimitData
import RHFormalization.DBFFGate2Overlap

/-!
# AdmissibleRouteHFWired — hF DISCHARGED: RH from exactly h_conv

ROUTE CARD
1. Target: derive the terminus's pointwise hF from the banked
   compact-uniform `admissible_F_stage_to_FHadmFree` (singleton compact),
   and close the frontier to EXACTLY h_conv.
2. This is the final wiring theorem: RiemannHypothesis from ONE
   hypothesis — the pillar. Everything else is kernel-discharged.
3. Raw B on Ω? NO. hComb/CompensatedB targeted? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter Metric

/-- Pointwise hF on RHP(1) from the banked compact-uniform limit,
via the singleton compact `{s}` (RHP(1) ⊆ Ω through the banked geometry). -/
theorem admissible_hF_pointwise
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ => galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
      Filter.atTop (nhds (FHadmFree s)) := by
  have hsΩ : s ∈ Ω := rightHalfPlane_one_subset_Omega hs
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact ({s} : Set ℂ) := isCompact_singleton
  have hKΩ : ({s} : Set ℂ) ⊆ Ω := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hsΩ
  have h := admissible_F_stage_to_FHadmFree ({s} : Set ℂ) hK hKΩ ε hε
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn s (Set.mem_singleton s)
  first
    | exact this
    | simpa [dist_comm] using this

/-- **THE PILLAR-ONLY TERMINUS**: RiemannHypothesis from exactly h_conv.
h_stage_holo, hB, hF are all discharged by banked theorems. -/
theorem RH_from_admissible_h_conv_only
    (RHcand : ℂ → ℂ)
    (h_conv :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ, s ∈ K →
              dist (galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
                (RHcand s) < ε) :
    RiemannHypothesis :=
  RH_from_admissible_route_conv_F
    RHcand
    h_conv
    (fun s hs => admissible_hF_pointwise s hs)

#print axioms admissible_hF_pointwise
#print axioms RH_from_admissible_h_conv_only

end

end RHFormalization
