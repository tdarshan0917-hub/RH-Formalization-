import RHFormalization.MontelUniqueLimit
import RHFormalization.DCanRemFromMontel
import Mathlib

/-!
# Holomorphic Montel — subsequence assembly (logic above Ascoli)

Isolates the logic of `HolomorphicMontelConvergence` ABOVE the Ascoli extraction step.
We name the Ascoli output as `AscoliExtraction` (every subsequence has a sub-subsequence
converging locally uniformly on Ω-compacts to a holomorphic limit), then prove — using the
banked identity-theorem uniqueness `eqOn_Omega_of_eqOn_open` — that this implies the full
`HolomorphicMontelConvergence` (loc-unif convergence to `RH`).

After this, the ONLY remaining Montel obligation is discharging `AscoliExtraction` from
`ArzelaAscoli.isCompact_of_equicontinuous` (the mechanical C(K,ℂ) bundling).

Part of discharging `HolomorphicMontelConvergence` (D.CAN-REM's last gap, p178).
-/

namespace RHFormalization
open Filter Topology Complex

/-- **Ascoli's clean output (named gap).** Every subsequence of `F` has a further
subsequence converging locally uniformly on Ω-compacts to some holomorphic limit. -/
def AscoliExtraction (F : ℕ → ℂ → ℂ) : Prop :=
  (∀ n, HolomorphicOnC (F n) Ω) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) →
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℂ → ℂ, HolomorphicOnC g Ω ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F (φ (ψ n)) s) (g s) < ε

/-- **Montel subsequence assembly.** -/
theorem holomorphicMontelConvergence_from_ascoli
    {F : ℕ → ℂ → ℂ} {RH : ℂ → ℂ}
    (hRH_holo : HolomorphicOnC RH Ω)
    (hAscoli : AscoliExtraction F) :
    HolomorphicMontelConvergence F RH := by
  intro h_holo h_bdd h_overlap K hK hKΩ ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  have hfreq : ∃ᶠ n in atTop, ∃ s ∈ K, ε ≤ dist (F n s) (RH s) := by
    refine hcon.mono ?_
    intro n hn
    simp only [not_forall, not_lt] at hn
    obtain ⟨s, hs, hd⟩ := hn
    exact ⟨s, hs, hd⟩
  obtain ⟨φ, hφ_mono, hφ_bad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, hψ_mono, g, hg_holo, hg_conv⟩ := hAscoli h_holo h_bdd φ hφ_mono
  obtain ⟨U, hUopen, hUne, hUsub, hUconv⟩ := h_overlap
  have hgRH : Set.EqOn g RH Ω := by
    apply eqOn_Omega_of_eqOn_open hg_holo hRH_holo hUopen hUne hUsub
    intro s hsU
    have hsΩ : s ∈ Ω := hUsub hsU
    have hsub_tendsto : Tendsto (fun n => F (φ (ψ n)) s) atTop (nhds (RH s)) := by
      have hmono : StrictMono (fun n => φ (ψ n)) := hφ_mono.comp hψ_mono
      exact (hUconv s hsU).comp hmono.tendsto_atTop
    have hg_tendsto : Tendsto (fun n => F (φ (ψ n)) s) atTop (nhds (g s)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      have hev := hg_conv {s} (isCompact_singleton) (Set.singleton_subset_iff.mpr hsΩ) δ hδ
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      exact ⟨N, fun n hn => hN n hn s (Set.mem_singleton s)⟩
    exact tendsto_nhds_unique hg_tendsto hsub_tendsto
  have hconv_RH : ∀ᶠ n in atTop, ∀ s ∈ K, dist (F (φ (ψ n)) s) (RH s) < ε := by
    have hgK := hg_conv K hK hKΩ ε hε
    filter_upwards [hgK] with n hn s hsK
    have : g s = RH s := hgRH (hKΩ hsK)
    rw [← this]; exact hn s hsK
  obtain ⟨n, hn⟩ := hconv_RH.exists
  obtain ⟨s, hsK, hbad⟩ := hφ_bad (ψ n)
  exact absurd (hn s hsK) (not_lt.mpr hbad)

#print axioms holomorphicMontelConvergence_from_ascoli

end RHFormalization
