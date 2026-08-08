import RHFormalization.HtailFrontier
import RHFormalization.SeamCoreReduction
import RHFormalization.CanonicalRcanStage
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-!
# HtailRouteCertificate — DIAGNOSTIC: hSC ⟹ HtailExists ⟹ RH
No new analytic hypotheses. Banked pieces only + the single hSC slot.
-/

/-- hSC gives loc-bdd of the canonical corrected family (defeq transfer). -/
theorem canonicalRcanStage_locbdd_of_hSC
    (hSC : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖canonicalRcanStage n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C, hC⟩ := correctedResidual_locbdd_of_seamCore hSC K hK hKΩ
  exact ⟨C, fun n s hs => by simpa [canonicalRcanStage] using hC n s hs⟩

/-- **Conditional Montel for the corrected family** (mirrors the banked
core extraction verbatim). -/
theorem canonicalRcan_compact_uniform_of_hSC
    (hSC : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C) :
    ∃ h : ℂ → ℂ, HolomorphicOnC h Ω ∧
      (∀ s ∈ RightHalfPlane (1 : ℝ),
        h s = FHadmFree s - galerkinBcanLimitData.Bcan s) := by
  have h_holo : ∀ n, HolomorphicOnC (canonicalRcanStage n) Ω :=
    fun n => canonicalRcanStage_holo n
  have h_bdd := canonicalRcanStage_locbdd_of_hSC hSC
  have hAsc : AscoliExtraction canonicalRcanStage :=
    ascoliExtraction_of_loc_bdd canonicalRcanStage h_bdd
  obtain ⟨ψ, hψ, h, hh_holo, hh_conv⟩ := hAsc h_holo h_bdd id strictMono_id
  refine ⟨h, hh_holo, ?_⟩
  intro s hs
  have hsΩ : s ∈ Ω := rightHalfPlane_one_subset_Omega hs
  have hsub_h : Tendsto (fun n => canonicalRcanStage (ψ n) s)
      atTop (𝓝 (h s)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hev := hh_conv {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr hsΩ) δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨N, fun n hn => hN n hn s (Set.mem_singleton s)⟩
  have hsub_lim : Tendsto (fun n => canonicalRcanStage (ψ n) s)
      atTop (𝓝 (FHadmFree s - galerkinBcanLimitData.Bcan s)) := by
    first
      | exact (canonicalRcanStage_overlap_tendsto s hs).comp hψ.tendsto_atTop
      | exact (canonicalRcanStage_overlap_tendsto s hs).comp
          (StrictMono.tendsto_atTop hψ)
  exact tendsto_nhds_unique hsub_h hsub_lim

/-- **THE ROUTE CERTIFICATE: hSC ⟹ HtailExists.** -/
theorem HtailExists_of_seamCore_locbdd
    (hSC : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C) :
    HtailExists := by
  obtain ⟨g, hg_holo, hg_over, _⟩ := galOmegaCore_compact_uniform
  obtain ⟨h, hh_holo, hh_over⟩ := canonicalRcan_compact_uniform_of_hSC hSC
  refine ⟨fun s => g s - h s, ?_, ?_⟩
  · intro z hz
    exact (hg_holo z hz).sub (hh_holo z hz)
  · intro s hs
    simp only []
    rw [hg_over s hs, hh_over s hs]
    unfold galOmegaCoreLimit
    ring

/-- **RH from the single open bound.** -/
theorem RH_of_seamCore_locbdd
    (hSC : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C) :
    RiemannHypothesis :=
  RH_from_Htail (HtailExists_of_seamCore_locbdd hSC)

#print axioms HtailExists_of_seamCore_locbdd
#print axioms RH_of_seamCore_locbdd

end

end RHFormalization
