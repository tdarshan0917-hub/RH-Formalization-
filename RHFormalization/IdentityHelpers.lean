import Mathlib

namespace RHFormalization
open Topology Filter Set

/-- A nonempty open set in ℂ contains a point distinct from any given x. -/
theorem open_nonempty_has_ne (o : Set ℂ) (ho : IsOpen o) (hne : o.Nonempty) (x : ℂ) :
    ∃ z ∈ o, z ≠ x := by
  rcases eq_or_ne hne.choose x with h | h
  · have hxo : x ∈ o := h ▸ hne.choose_spec
    have hmem : o ∈ 𝓝[≠] x := mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hxo)
    have hsub : o ∩ {x}ᶜ ∈ 𝓝[≠] x :=
      Filter.inter_mem hmem self_mem_nhdsWithin
    obtain ⟨z, hzo, hzx⟩ := Filter.nonempty_of_mem hsub
    exact ⟨z, hzo, by simpa using hzx⟩
  · exact ⟨hne.choose, hne.choose_spec, h⟩

/-- Punctured equality of meromorphic functions gives full-neighborhood equality
of their normal forms. This is the valid meromorphic-germ statement. -/
theorem mero_nf_full {f g : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
    (h : f =ᶠ[𝓝[≠] x] g) :
    (toMeromorphicNFAt f x) =ᶠ[𝓝 x] (toMeromorphicNFAt g x) := by
  have hnf_f : f =ᶠ[𝓝[≠] x] (toMeromorphicNFAt f x) :=
    hf.eq_nhdsNE_toMeromorphicNFAt
  have hnf_g : g =ᶠ[𝓝[≠] x] (toMeromorphicNFAt g x) :=
    hg.eq_nhdsNE_toMeromorphicNFAt
  have hNFf : MeromorphicNFAt (toMeromorphicNFAt f x) x :=
    meromorphicNFAt_toMeromorphicNFAt
  have hNFg : MeromorphicNFAt (toMeromorphicNFAt g x) x :=
    meromorphicNFAt_toMeromorphicNFAt
  have hpunct :
      (toMeromorphicNFAt f x) =ᶠ[𝓝[≠] x] (toMeromorphicNFAt g x) :=
    (hnf_f.symm.trans h).trans hnf_g
  exact (hNFf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hNFg).mp hpunct

end RHFormalization
