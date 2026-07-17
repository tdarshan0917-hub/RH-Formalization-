import RHFormalization.AscoliLocBddBridge

/-!
# THE FINAL COLLAPSE: RH from `h_loc_bdd` ALONE

The continued object `Bω` need not be supplied: the banked Ascoli
extraction PRODUCES a holomorphic subsequential limit `g` of the
admissible B-stages, and the banked overlap convergence (`admissible_hB`)
forces `g = Bcan` on `RightHalfPlane 1`.  Feeding `(g, hg_holo, hover)`
into the frozen endpoint leaves exactly ONE hypothesis:

> **h_loc_bdd** — uniform-in-`n` boundedness of the admissible B-stages
> on Ω-compacts (the manuscript's S(t,R) density-normalized anchor).

This is the manuscript's central analytic claim, now isolated as the
single remaining input to RiemannHypothesis.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- **RH from the S(t,R) anchor alone.** -/
theorem RH_from_admissible_locbdd_only
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖admissibleBStageFamily n s‖ ≤ C) :
    RiemannHypothesis := by
  have hAsc : AscoliExtraction admissibleBStageFamily :=
    ascoliExtraction_of_loc_bdd admissibleBStageFamily h_loc_bdd
  obtain ⟨ψ, hψ, g, hg_holo, hg_conv⟩ :=
    hAsc admissibleBStageFamily_holo h_loc_bdd id strictMono_id
  have hover : ∀ s ∈ RightHalfPlane (1 : ℝ),
      g s = galerkinBcanLimitData.Bcan s := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      first
        | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num) hs
        | exact rightHalfPlane_subset_Omega 1 one_pos hs
        | exact rightHalfPlane_subset_Omega _ (by norm_num) hs
    have h1 : Tendsto (fun n => admissibleBStageFamily (id (ψ n)) s)
        atTop (𝓝 (g s)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have h := hg_conv {s} isCompact_singleton
        (Set.singleton_subset_iff.mpr hsΩ) ε hε
      filter_upwards [h] with n hn
      first
        | exact hn s rfl
        | exact hn s (Set.mem_singleton s)
    have h2 : Tendsto (fun n => admissibleBStageFamily (ψ n) s)
        atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
      first
        | exact (admissible_hB s hs).comp hψ.tendsto_atTop
        | exact (admissible_hB s hs).comp (StrictMono.tendsto_atTop hψ)
    have h1' : Tendsto (fun n => admissibleBStageFamily (ψ n) s)
        atTop (𝓝 (g s)) := by
      first
        | exact h1
        | (simpa only [id_eq] using h1)
        | (simpa only [Function.id_def] using h1)
        | (simpa using h1)
    exact tendsto_nhds_unique h1' h2
  exact RH_from_admissible_B_locbdd g hg_holo hover h_loc_bdd

#print axioms RH_from_admissible_locbdd_only

end

end RHFormalization
