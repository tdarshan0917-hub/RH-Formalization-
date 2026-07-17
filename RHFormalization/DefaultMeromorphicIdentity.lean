import RHFormalization.GlobalMeromorphicIdentity
import RHFormalization.IdentityHelpers

namespace RHFormalization
noncomputable section
open Complex Topology Filter Set

def defaultMeromorphicIdentityPrincipleAPI : MeromorphicIdentityPrincipleAPI :=
{ h_identity := by
    intro f g U V hUconn hVopen hVne hVsub hfU hgU hVeq
    -- T : punctured-agreement set; open.
    set T : Set ℂ := {x | f =ᶠ[𝓝[≠] x] g} with hT
    have hTopen : IsOpen T := isOpen_setOf_eventually_nhdsWithin
    have hVT : ∀ x ∈ V, x ∈ T := by
      intro x hxV
      have hfull : ∀ᶠ y in 𝓝 x, f y = g y :=
        eventually_of_mem (hVopen.mem_nhds hxV) (fun y hy => hVeq hy)
      exact hfull.filter_mono nhdsWithin_le_nhds
    -- closure T ∩ U ⊆ T
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
    -- Conclude EqOn: at each x ∈ U, f - g is meromorphic and eventually 0 on 𝓝[≠]x,
    -- hence eventually 0 on 𝓝 x (full), giving f x = g x.
    intro x hxU
    have hfx : MeromorphicAt f x := hfU x hxU
    have hgx : MeromorphicAt g x := hgU x hxU
    have hpunct : f =ᶠ[𝓝[≠] x] g := hUsubT hxU
    have hsub_mero : MeromorphicAt (f - g) x := hfx.sub hgx
    have hzero_ne : (f - g) =ᶠ[𝓝[≠] x] 0 := by
      filter_upwards [hpunct] with w hw
      simp [Pi.sub_apply, hw]
    -- meromorphic + eventually zero on punctured ⟹ eventually zero on full nbhd
    have hzero_full : (f - g) =ᶠ[𝓝 x] 0 := by
      -- f - g is meromorphic at x and equals 0 on the punctured neighborhood.
      -- Step 1: its normal form is 0 on the full neighborhood.
      have hNFfg : MeromorphicNFAt (toMeromorphicNFAt (f - g) x) x :=
        meromorphicNFAt_toMeromorphicNFAt
      have hNF0 : MeromorphicNFAt (0 : ℂ → ℂ) x := by
        simpa using (analyticAt_const (v := (0:ℂ))).meromorphicNFAt
      have he1 : (f - g) =ᶠ[𝓝[≠] x] (toMeromorphicNFAt (f - g) x) :=
        hsub_mero.eq_nhdsNE_toMeromorphicNFAt
      have hpz : (toMeromorphicNFAt (f - g) x) =ᶠ[𝓝[≠] x] (0 : ℂ → ℂ) :=
        he1.symm.trans hzero_ne
      have hfullNF : (toMeromorphicNFAt (f - g) x) =ᶠ[𝓝 x] (0 : ℂ → ℂ) :=
        (hNFfg.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hNF0).mp hpz
      -- Step 2: the normal form is analytic at x (it is eventually 0), so order ≥ 0.
      have hNFan : AnalyticAt ℂ (toMeromorphicNFAt (f - g) x) x :=
        (analyticAt_congr hfullNF).mpr analyticAt_const
      have hordfg : 0 ≤ meromorphicOrderAt (f - g) x := by
        have hcongr : meromorphicOrderAt (f - g) x
            = meromorphicOrderAt (toMeromorphicNFAt (f - g) x) x :=
          meromorphicOrderAt_congr he1
        rw [hcongr]
        exact hNFan.meromorphicOrderAt_nonneg
      -- Step 3: order ≥ 0 ⇒ f - g converges on the punctured nbhd; the limit is 0.
      obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hsub_mero hordfg
      have hc0 : c = 0 := by
        have hz : Tendsto (f - g) (𝓝[≠] x) (𝓝 (0:ℂ)) :=
          tendsto_const_nhds.congr' hzero_ne.symm
        exact tendsto_nhds_unique hc hz
      subst hc0
      -- Step 4: f - g is eventually 0 on the punctured nbhd, so its order is ⊤,
      -- which gives eventually 0 on the FULL nbhd directly.
      have htop : meromorphicOrderAt (f - g) x = ⊤ := by
        rw [meromorphicOrderAt_eq_top_iff]
        exact hzero_ne
      exact (meromorphicOrderAt_eq_top_iff.mp htop)
    have hval : (f - g) x = 0 := hzero_full.eq_of_nhds
    have hfg : f x - g x = 0 := by simpa [Pi.sub_apply] using hval
    exact sub_eq_zero.mp hfg }
end
end RHFormalization
