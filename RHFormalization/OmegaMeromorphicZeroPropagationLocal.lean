import RHFormalization.OmegaMeromorphicZeroPropagationProof

/-!
# RHFormalization.OmegaMeromorphicZeroPropagationLocal

Local stability lemmas for the remaining Appendix-F zero-propagation theorem.

These are genuine proof steps toward `OmegaMeromorphicZeroPropagationAPI`, not
endpoint wrappers.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
If `H` is zero on a punctured neighbourhood of `z₀`, then every nearby punctured
point `z` also has a punctured neighbourhood on which `H` is zero.
-/
theorem zero_germ_stable_eventually_nhdsNE
    {H : ℂ → ℂ}
    {z₀ : ℂ}
    (hlocal : H =ᶠ[𝓝[≠] z₀] (fun _ : ℂ => 0)) :
    ∀ᶠ z in 𝓝[≠] z₀,
      H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0) := by
  have hlocal_ev :
      ∀ᶠ w in 𝓝[≠] z₀, H w = 0 := by
    simpa [Filter.EventuallyEq] using hlocal

  rw [eventually_nhdsWithin_iff] at hlocal_ev
  rw [eventually_nhds_iff] at hlocal_ev
  rcases hlocal_ev with ⟨t, ht_zero, ht_open, hz₀t⟩

  rw [eventually_nhdsWithin_iff]
  filter_upwards [ht_open.mem_nhds hz₀t] with z hzt hz_ne

  have hcompl_open : IsOpen ({z₀}ᶜ : Set ℂ) :=
    isClosed_singleton.isOpen_compl

  have ht_nhds : t ∈ 𝓝 z :=
    ht_open.mem_nhds hzt

  have hcompl_nhds : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z :=
    hcompl_open.mem_nhds hz_ne

  have hsmall_nhds : t ∩ {z₀}ᶜ ∈ 𝓝 z :=
    Filter.inter_mem ht_nhds hcompl_nhds

  have hsmall_nhdsNE : t ∩ {z₀}ᶜ ∈ 𝓝[≠] z :=
    (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z) hsmall_nhds

  have h_ev :
      ∀ᶠ y in 𝓝[≠] z, H y = 0 := by
    filter_upwards [hsmall_nhdsNE] with y hy
    exact ht_zero y hy.1 hy.2

  simpa [Filter.EventuallyEq] using h_ev

/--
The set of points with a punctured zero-germ is open.
-/
theorem isOpen_zeroGermSet
    (H : ℂ → ℂ) :
    IsOpen {z : ℂ | H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0)} := by
  rw [isOpen_iff_eventually]
  intro z hz

  have hstab :=
    zero_germ_stable_eventually_nhdsNE
      (H := H)
      (z₀ := z)
      hz

  rw [eventually_nhdsWithin_iff] at hstab

  filter_upwards [hstab] with y hy
  by_cases hyz : y = z
  · simpa [hyz] using hz
  · exact hy (by simpa [hyz])

/--
If `H` is eventually nonzero on a punctured neighbourhood of `z₀`, then every
nearby punctured point `z` also has a punctured neighbourhood on which `H` is
nonzero.
-/
theorem nonzero_germ_stable_eventually_nhdsNE
    {H : ℂ → ℂ}
    {z₀ : ℂ}
    (hlocal : ∀ᶠ w in 𝓝[≠] z₀, H w ≠ 0) :
    ∀ᶠ z in 𝓝[≠] z₀,
      ∀ᶠ w in 𝓝[≠] z, H w ≠ 0 := by
  rw [eventually_nhdsWithin_iff] at hlocal
  rw [eventually_nhds_iff] at hlocal
  rcases hlocal with ⟨t, ht_nonzero, ht_open, hz₀t⟩

  rw [eventually_nhdsWithin_iff]
  filter_upwards [ht_open.mem_nhds hz₀t] with z hzt hz_ne

  have hcompl_open : IsOpen ({z₀}ᶜ : Set ℂ) :=
    isClosed_singleton.isOpen_compl

  have ht_nhds : t ∈ 𝓝 z :=
    ht_open.mem_nhds hzt

  have hcompl_nhds : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z :=
    hcompl_open.mem_nhds hz_ne

  have hsmall_nhds : t ∩ {z₀}ᶜ ∈ 𝓝 z :=
    Filter.inter_mem ht_nhds hcompl_nhds

  have hsmall_nhdsNE : t ∩ {z₀}ᶜ ∈ 𝓝[≠] z :=
    (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z) hsmall_nhds

  filter_upwards [hsmall_nhdsNE] with y hy
  exact ht_nonzero y hy.1 hy.2

/--
The set of points with a punctured nonzero-germ is open.
-/
theorem isOpen_nonzeroGermSet
    (H : ℂ → ℂ) :
    IsOpen {z : ℂ | ∀ᶠ w in 𝓝[≠] z, H w ≠ 0} := by
  rw [isOpen_iff_eventually]
  intro z hz

  have hstab :=
    nonzero_germ_stable_eventually_nhdsNE
      (H := H)
      (z₀ := z)
      hz

  rw [eventually_nhdsWithin_iff] at hstab

  filter_upwards [hstab] with y hy
  by_cases hyz : y = z
  · simpa [hyz] using hz
  · exact hy (by simpa [hyz])

end

end RHFormalization
