-- SENTINEL: compensated-decisive-v1
import RHFormalization.AscoliLocBddBridge
import RHFormalization.DecodedFlatTerminus
import RHFormalization.DBFFCompensator
import RHFormalization.DBFFCompensatorHolo
import RHFormalization.AdmissibleGalerkinEndpoint
import RHFormalization.AdmissibleFreeFH
import Mathlib

/-!
# THE DECISIVE ENDPOINT — RH from loc-bdd of the COMPENSATED B family
Family: Bc n := B_stage(adm n) − compensatorM n — the corrected object
(C3/O3; numerically flat over five decades). Raw-B and raw-R loc-bdd are
unsatisfiable (kills on record); this is the satisfiable-shaped single
hypothesis. Producer skeleton harvested from AdmissibleLocBddOnly (banked).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- The compensated admissible B family. -/
def compensatedBFamily (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s - compensatorM n s

theorem compensatedBFamily_holo (n : ℕ) :
    HolomorphicOnC (compensatedBFamily n) Ω := by
  first
    | exact (admissible_B_stage_holo n).sub (compensatorM_holo n)
    | exact HolomorphicOnC.sub (admissible_B_stage_holo n) (compensatorM_holo n)

/-- **RH from ONE hypothesis: the compensated-B anchor.** -/
theorem RH_from_compensatedB_locbdd
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖compensatedBFamily n s‖ ≤ C) :
    RiemannHypothesis := by
  have hAsc : AscoliExtraction compensatedBFamily :=
    ascoliExtraction_of_loc_bdd compensatedBFamily h_loc_bdd
  obtain ⟨ψ, hψ, g, hg_holo, hg_conv⟩ :=
    hAsc compensatedBFamily_holo h_loc_bdd id strictMono_id
  have hover : ∀ s ∈ RightHalfPlane (1 : ℝ),
      g s = galerkinBcanLimitData.Bcan s := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      first
        | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num) hs
        | exact rightHalfPlane_subset_Omega 1 one_pos hs
        | exact rightHalfPlane_subset_Omega _ (by norm_num) hs
    have h1 : Tendsto (fun n => compensatedBFamily (id (ψ n)) s)
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
          (admissibleGalerkinStageSeq (ψ n)) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
      first
        | exact (admissible_hB s hs).comp hψ.tendsto_atTop
        | exact (admissible_hB s hs).comp (StrictMono.tendsto_atTop hψ)
    have hM : Tendsto (fun n => compensatorM (ψ n) s) atTop (𝓝 (0:ℂ)) := by
      first
        | exact (compensatorM_overlap0 hs).comp hψ.tendsto_atTop
        | exact (compensatorM_overlap0 hs).comp (StrictMono.tendsto_atTop hψ)
    have h2 : Tendsto (fun n => compensatedBFamily (ψ n) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
      have := hB.sub hM
      simpa [compensatedBFamily] using this
    have h1' : Tendsto (fun n => compensatedBFamily (ψ n) s)
        atTop (𝓝 (g s)) := by
      first
        | exact h1
        | (simpa only [id_eq] using h1)
        | (simpa using h1)
    exact tendsto_nhds_unique h1' h2
  -- feed the flat terminus: R_H := FHadmFree − g
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

#print axioms compensatedBFamily
#print axioms RH_from_compensatedB_locbdd

end

end RHFormalization
