import RHFormalization.GalOmegaCoreOverlapLimit
import RHFormalization.AscoliLocBddBridge
import RHFormalization.MontelSubsequenceAssembly

/-!
# GalOmegaCoreCompactUniform — THE FIRST UNCONDITIONAL CONVERGENCE

ROUTE CARD
1. Target: ∃ g ∈ O(Ω): g = coreLimit on RHP(1), and galOmegaCore → g
   locally uniformly on Ω-compacts. ZERO hypotheses — holo, loc-bdd,
   Ascoli, Montel, overlap limit are ALL banked theorems.
2. Consumer: the ledger transfer R_stage = core − tail toward h_conv.
3. Raw B on Ω? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **UNCONDITIONAL compact-uniform convergence of the Ω-core.** -/
theorem galOmegaCore_compact_uniform :
    ∃ g : ℂ → ℂ, HolomorphicOnC g Ω ∧
      (∀ s ∈ RightHalfPlane (1 : ℝ), g s = galOmegaCoreLimit s) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ, s ∈ K → dist (galOmegaCore n s) (g s) < ε := by
  have h_holo : ∀ n, HolomorphicOnC (galOmegaCore n) Ω :=
    fun n => galOmegaCore_holo n
  have h_bdd := galOmegaCore_loc_bdd
  have hAsc : AscoliExtraction galOmegaCore :=
    ascoliExtraction_of_loc_bdd galOmegaCore h_bdd
  obtain ⟨ψ, hψ, g, hg_holo, hg_conv⟩ :=
    hAsc h_holo h_bdd id strictMono_id
  -- g agrees with the banked overlap limit on RHP(1)
  have hover : ∀ s ∈ RightHalfPlane (1 : ℝ), g s = galOmegaCoreLimit s := by
    intro s hs
    have hsΩ : s ∈ Ω := rightHalfPlane_one_subset_Omega hs
    have hsub_g : Tendsto (fun n => galOmegaCore (id (ψ n)) s)
        atTop (𝓝 (g s)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      have hev := hg_conv {s} isCompact_singleton
        (Set.singleton_subset_iff.mpr hsΩ) δ hδ
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      exact ⟨N, fun n hn => hN n hn s (Set.mem_singleton s)⟩
    have hsub_lim : Tendsto (fun n => galOmegaCore (ψ n) s)
        atTop (𝓝 (galOmegaCoreLimit s)) := by
      first
        | exact (galOmegaCore_overlap_limit s hs).comp hψ.tendsto_atTop
        | exact (galOmegaCore_overlap_limit s hs).comp
            (StrictMono.tendsto_atTop hψ)
    have hsub_g' : Tendsto (fun n => galOmegaCore (ψ n) s)
        atTop (𝓝 (g s)) := by
      first
        | exact hsub_g
        | (simpa only [id_eq] using hsub_g)
        | (simpa using hsub_g)
    exact tendsto_nhds_unique hsub_g' hsub_lim
  refine ⟨g, hg_holo, hover, ?_⟩
  have hmontel := holomorphicMontelConvergence_from_ascoli
    (F := galOmegaCore) (RH := g) hg_holo hAsc
  apply hmontel h_holo h_bdd
  refine ⟨{s : ℂ | 1 < s.re}, ?_, ⟨(2:ℂ), by norm_num⟩, ?_, ?_⟩
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro s hs
    have hs1 : s ∈ RightHalfPlane (1 : ℝ) := hs
    exact rightHalfPlane_one_subset_Omega hs1
  · intro s hs
    have hs1 : s ∈ RightHalfPlane (1 : ℝ) := hs
    have h := galOmegaCore_overlap_limit s hs1
    rw [← hover s hs1] at h
    exact h

#print axioms galOmegaCore_compact_uniform

end

end RHFormalization
