import RHFormalization.GlobalMeromorphicIdentity
import RHFormalization.IdentityHelpers

namespace RHFormalization

noncomputable section

open Complex Topology Filter Set

theorem meromorphic_punctured_identity
    (f g : ℂ → ℂ) (U V : Set ℂ)
    (hUconn : IsPreconnected U)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVsub : V ⊆ U)
    (hfU : MeromorphicOnC f U) (hgU : MeromorphicOnC g U)
    (hVeq : Set.EqOn f g V)
    (x : ℂ) (hxU : x ∈ U) :
    f =ᶠ[𝓝[≠] x] g := by
  set T : Set ℂ := {x | f =ᶠ[𝓝[≠] x] g} with hT
  have hTopen : IsOpen T := isOpen_setOf_eventually_nhdsWithin
  have hVT : ∀ x ∈ V, x ∈ T := by
    intro x hxV
    have hfull : ∀ᶠ y in 𝓝 x, f y = g y :=
      eventually_of_mem (hVopen.mem_nhds hxV) (fun y hy => hVeq hy)
    exact hfull.filter_mono nhdsWithin_le_nhds
  have hmain : closure T ∩ U ⊆ T := by
    rintro x ⟨hxcl, hxU⟩
    have hfx : MeromorphicAt f x := hfU x hxU
    have hgx : MeromorphicAt g x := hgU x hxU
    have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = g z := by
      rw [frequently_iff]
      intro s hs
      rw [mem_nhdsWithin] at hs
      obtain ⟨o, hoopen, hxo, hosub⟩ := hs
      have hoTopen : IsOpen (o ∩ T) := hoopen.inter hTopen
      have hneo : (o ∩ T).Nonempty := by
        rw [mem_closure_iff] at hxcl
        obtain ⟨w, hwo, hwT⟩ := hxcl o hoopen hxo
        exact ⟨w, hwo, hwT⟩
      obtain ⟨z, hzoT, hzx⟩ := open_nonempty_has_ne (o ∩ T) hoTopen hneo x
      have hzT : z ∈ T := hzoT.2
      have hzo : z ∈ o := hzoT.1
      have hfreqz : ∃ᶠ w in 𝓝[≠] z, f w = g w ∧ w ∈ o ∧ w ≠ x := by
        have h1 : ∀ᶠ w in 𝓝[≠] z, f w = g w := hzT
        have h2 : ∀ᶠ w in 𝓝[≠] z, w ∈ o :=
          mem_nhdsWithin_of_mem_nhds (hoopen.mem_nhds hzo)
        have h3 : ∀ᶠ w in 𝓝[≠] z, w ≠ x :=
          mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hzx)
        exact ((h1.and h2).and h3).frequently.mono
          (fun w hw => ⟨hw.1.1, hw.1.2, hw.2⟩)
      obtain ⟨w, hwfg, hwo, hwx⟩ := hfreqz.exists
      exact ⟨w, hosub ⟨hwo, hwx⟩, hwfg⟩
    show f =ᶠ[𝓝[≠] x] g
    exact (hfx.frequently_eq_iff_eventuallyEq hgx).mp hfreq
  have hUsubT : U ⊆ T :=
    hUconn.subset_of_closure_inter_subset hTopen
      ⟨_, hVsub hVne.choose_spec, hVT _ hVne.choose_spec⟩ hmain
  exact hUsubT hxU

#print axioms meromorphic_punctured_identity

end

end RHFormalization
