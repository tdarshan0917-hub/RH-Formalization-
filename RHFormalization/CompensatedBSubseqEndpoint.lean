import RHFormalization.CompensatedBDecisiveEndpoint
import Mathlib

/-!
# CompensatedBSubseqEndpoint — PL-6a: the decisive endpoint along a subsequence

`RH_from_compensatedB_locbdd` asks for local boundedness of the compensated family at
every stage. Its proof only uses a strictly increasing sequence of stages: Montel
extracts a further subsequence, and the Re s > 1 identification passes to subsequences.
This file proves the endpoint for any strictly increasing stage sequence `σ`, so the
polylog route can supply bounds only at the square stages n = M² − 2.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- **RH from local boundedness of the compensated family along any increasing sequence of stages.** -/
theorem RH_from_compensatedB_locbdd_subseq (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ M, ∀ s ∈ K, ‖compensatedBFamily (σ M) s‖ ≤ C) :
    RiemannHypothesis := by
  have hAsc : AscoliExtraction (fun M => compensatedBFamily (σ M)) :=
    ascoliExtraction_of_loc_bdd (fun M => compensatedBFamily (σ M)) h_loc_bdd
  obtain ⟨ψ, hψ, g, hg_holo, hg_conv⟩ :=
    hAsc (fun M => compensatedBFamily_holo (σ M)) h_loc_bdd id strictMono_id
  have hσψ : StrictMono (fun n => σ (ψ n)) := hσ.comp hψ
  have hover : ∀ s ∈ RightHalfPlane (1 : ℝ),
      g s = galerkinBcanLimitData.Bcan s := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      first
        | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num) hs
        | exact rightHalfPlane_subset_Omega 1 one_pos hs
        | exact rightHalfPlane_subset_Omega _ (by norm_num) hs
    have h1 : Tendsto (fun n => compensatedBFamily (σ (ψ n)) s)
        atTop (𝓝 (g s)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have h := hg_conv {s} isCompact_singleton
        (Set.singleton_subset_iff.mpr hsΩ) ε hε
      filter_upwards [h] with n hn
      first
        | exact hn s rfl
        | exact hn s (Set.mem_singleton s)
    have hB : Tendsto (fun n => galerkinStagePackage.B_stage
          (admissibleGalerkinStageSeq (σ (ψ n))) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) :=
      (admissible_hB s hs).comp hσψ.tendsto_atTop
    have hM : Tendsto (fun n => compensatorM (σ (ψ n)) s) atTop (𝓝 (0:ℂ)) :=
      (compensatorM_overlap0 hs).comp hσψ.tendsto_atTop
    have h2 : Tendsto (fun n => compensatedBFamily (σ (ψ n)) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
      have := hB.sub hM
      simpa [compensatedBFamily] using this
    exact tendsto_nhds_unique h1 h2
  refine RH_from_holomorphic_remainder (fun s => FHadmFree s - g s) ?_ ?_
  · first
      | exact FHadmFree_holo.sub hg_holo
      | exact (FHadmFree_holo_on_Omega).sub hg_holo
      | exact HolomorphicOnC.sub FHadmFree_holo hg_holo
  · intro s hs
    have h := hover s hs
    show FHadmFree s = galerkinBcanLimitData.Bcan s + (FHadmFree s - g s)
    rw [← h]
    ring

#print axioms RH_from_compensatedB_locbdd_subseq

end

end RHFormalization
