import RHFormalization.AdmissibleRStageOverlapLimit
import RHFormalization.AscoliLocBddBridge
import RHFormalization.MontelSubsequenceAssembly

/-!
# AdmissibleHConvFromRLocBdd — h_conv from R-family loc-bdd; RH from loc-bdd

ROUTE CARD
1. Target: compose banked Ascoli + Montel + the banked overlap anchor into
   `h_conv` for the admissible R-family, from ONE hypothesis: loc-bdd of
   the R-stages on Ω-compacts. Then feed the terminus:
   `RH_from_admissible_R_locbdd (h_loc_bdd) : RiemannHypothesis`.
2. This targets the R-FAMILY, not B (the B-locbdd endpoint is a known
   mirage: B-tail unbounded at depth). R is the canonical remainder the
   manuscript's D.MR.2 bounds by sectors.
3. Raw B on Ω? NO. hComb/CompensatedB targeted? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- The admissible R-stage family. -/
def admissibleRStageFamily (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s

/-- **h_conv from loc-bdd of the R-family.** -/
theorem admissible_h_conv_from_R_locbdd
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖admissibleRStageFamily n s‖ ≤ C) :
    ∃ RHcand : ℂ → ℂ,
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ, s ∈ K →
              dist (admissibleRStageFamily n s) (RHcand s) < ε := by
  have hF_holo : ∀ n, HolomorphicOnC (admissibleRStageFamily n) Ω :=
    fun n => admissible_R_stage_holo n
  have hAsc : AscoliExtraction admissibleRStageFamily :=
    ascoliExtraction_of_loc_bdd admissibleRStageFamily h_loc_bdd
  obtain ⟨ψ, hψ, g, hg_holo, hg_conv⟩ :=
    hAsc hF_holo h_loc_bdd id strictMono_id
  refine ⟨g, ?_⟩
  have hmontel := holomorphicMontelConvergence_from_ascoli
    (F := admissibleRStageFamily) (RH := g) hg_holo hAsc
  apply hmontel hF_holo h_loc_bdd
  -- the open-overlap witness: U = {re > 1}
  refine ⟨{s : ℂ | 1 < s.re}, ?_, ⟨(2:ℂ), by norm_num⟩, ?_, ?_⟩
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro s hs
    have hs1 : s ∈ RightHalfPlane (1 : ℝ) := hs
    exact rightHalfPlane_one_subset_Omega hs1
  · intro s hs
    have hs1 : s ∈ RightHalfPlane (1 : ℝ) := hs
    have hsΩ : s ∈ Ω := rightHalfPlane_one_subset_Omega hs1
    -- full sequence → RHcand on the overlap (banked anchor)
    have hfull := admissible_R_stage_overlap_limit s hs1
    -- subsequence → g at s (from the extraction on the singleton)
    have hsub_g : Tendsto (fun n => admissibleRStageFamily (id (ψ n)) s)
        atTop (𝓝 (g s)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      have hev := hg_conv {s} isCompact_singleton
        (Set.singleton_subset_iff.mpr hsΩ) δ hδ
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      exact ⟨N, fun n hn => hN n hn s (Set.mem_singleton s)⟩
    -- subsequence → RHcand at s (compose full with strict mono)
    have hsub_R : Tendsto (fun n => admissibleRStageFamily (ψ n) s)
        atTop (𝓝 (admissibleRHcand s)) := by
      first
        | exact hfull.comp hψ.tendsto_atTop
        | exact hfull.comp (StrictMono.tendsto_atTop hψ)
    have hsub_g' : Tendsto (fun n => admissibleRStageFamily (ψ n) s)
        atTop (𝓝 (g s)) := by
      first
        | exact hsub_g
        | (simpa only [id_eq] using hsub_g)
        | (simpa using hsub_g)
    have hgs : g s = admissibleRHcand s := tendsto_nhds_unique hsub_g' hsub_R
    rw [hgs]
    exact hfull

/-- **RH FROM R-FAMILY LOC-BDD ALONE.** The last named Prop before the
knife-edge: prove this boundedness, get RiemannHypothesis. -/
theorem RH_from_admissible_R_locbdd
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖admissibleRStageFamily n s‖ ≤ C) :
    RiemannHypothesis := by
  obtain ⟨RHcand, hconv⟩ := admissible_h_conv_from_R_locbdd h_loc_bdd
  exact RH_from_admissible_h_conv_only RHcand hconv

#print axioms admissible_h_conv_from_R_locbdd
#print axioms RH_from_admissible_R_locbdd

end

end RHFormalization
