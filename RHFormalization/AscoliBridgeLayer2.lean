import RHFormalization.AscoliBridgeLayer1
import Mathlib

/-!
# Ascoli bridge, layer 2: C(↥Ω,ℂ)-convergence ⟹ loc-unif dist form on Ω-compacts

Unpacks convergence `H → gC` in `C(↥Ω, ℂ)` into the
`∀ K compact ⊆ Ω, ∀ ε>0, ∀ᶠ n, ∀ s ∈ K, dist (...) < ε` form, via
`tendsto_iff_forall_isCompact_tendstoUniformlyOn` + the subtype-compact correspondence.
-/

namespace RHFormalization
open Filter Topology Complex

/-- C(↥Ω,ℂ)-convergence gives the locally-uniform dist bound on every compact `K ⊆ Ω`. -/
theorem ascoli_C_tendsto_to_locunif
    {H : ℕ → C(Ω, ℂ)} {gC : C(Ω, ℂ)}
    (hconv : Tendsto H atTop (nhds gC))
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s : ℂ, ∀ hs : s ∈ Ω, s ∈ K →
      dist ((H n) ⟨s, hs⟩) (gC ⟨s, hs⟩) < ε := by
  set K' : Set (Ω : Set ℂ) := Subtype.val ⁻¹' K with hK'def
  have hK'_compact : IsCompact K' := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' K' = K := by
      rw [hK'def, Subtype.image_preimage_val]
      exact Set.inter_eq_right.mpr hKΩ
    rw [this]; exact hK
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at hconv
  have hunif := hconv K' hK'_compact
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hev := hunif ε hε
  filter_upwards [hev] with n hn
  intro s hs hsK
  have hmem : (⟨s, hs⟩ : (Ω : Set ℂ)) ∈ K' := hsK
  have := hn ⟨s, hs⟩ hmem
  rw [dist_comm] at this
  exact this

#print axioms ascoli_C_tendsto_to_locunif

end RHFormalization
