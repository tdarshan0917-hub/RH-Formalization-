import RHFormalization.AdmissibleDFHLimitData
import Mathlib

/-!
# GalerkinFStageUniformBound — F-side of h_eps_bdd, CLOSED

`‖F_stage (admissibleGalerkinStageSeq n) s‖ ≤ C` uniformly in `n`, `s ∈ K ⋐ Ω`.

From banked facts only:
* `admissible_F_stage_to_FHadmFree` — uniform convergence on Ω-compacts
* `FHadmFree_holo`                  — limit holomorphic ⟹ bounded on K
* `galerkinStagePackage_F_stage_holo_admissible` — each stage bounded on K
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Filter Topology

/-- Sup of `‖·‖` of a holomorphic function on an Ω-compact. -/
theorem exists_bound_of_holo_on_compact (f : ℂ → ℂ) (hf : HolomorphicOnC f Ω)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ K, ‖f s‖ ≤ M := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨0, le_rfl, by simp [hemp]⟩
  · have hcont : ContinuousOn f K := (hf.mono hKΩ).continuousOn
    obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hcont.norm
    exact ⟨‖f x‖, norm_nonneg _, fun s hs => hmax hs⟩

/-- **F-SIDE OF h_eps_bdd.** The genuine package F-slot is uniformly bounded
on Ω-compacts along the admissible net. -/
theorem F_stage_uniform_bound_on_compacts
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (s : ℂ), s ∈ K →
      ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_holo_on_compact FHadmFree FHadmFree_holo K hK hKΩ
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (admissible_F_stage_to_FHadmFree K hK hKΩ 1 one_pos)
  -- head: each of the finitely many stages n < N₀ is bounded on K
  have hhead : ∀ n : ℕ, ∃ Mn : ℝ, 0 ≤ Mn ∧ ∀ s ∈ K,
      ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖ ≤ Mn :=
    fun n => exists_bound_of_holo_on_compact _
      (galerkinStagePackage_F_stage_holo_admissible n) K hK hKΩ
  choose Mn hMn0 hMn using hhead
  obtain ⟨B, hB⟩ := Finset.exists_le ((Finset.range N₀).image Mn)
  refine ⟨max B (1 + M), le_trans hM0 (by
    have : M ≤ 1 + M := by linarith
    exact le_trans this (le_max_right _ _)), fun n s hs => ?_⟩
  rcases lt_or_ge n N₀ with hlt | hge
  · refine le_trans (hMn n s hs) (le_trans ?_ (le_max_left _ _))
    exact hB _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hlt))
  · have hd := hN₀ n hge s hs
    rw [dist_eq_norm] at hd
    have h1 : ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖
        ≤ ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
            - FHadmFree s‖ + ‖FHadmFree s‖ := by
      have := norm_add_le
        (galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s - FHadmFree s)
        (FHadmFree s)
      simpa using this
    have h2 := hM s hs
    refine le_trans ?_ (le_max_right B (1 + M))
    linarith [hd.le]

#print axioms exists_bound_of_holo_on_compact
#print axioms F_stage_uniform_bound_on_compacts

end RHFormalization
