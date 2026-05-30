import RHFormalization.OmegaMeromorphicZeroPropagationLocal

/-!
# RHFormalization.OmegaMeromorphicZeroPropagationClopen

Completes the preconnectedness step for the remaining Appendix-F zero-propagation
theorem.

This is real proof work toward `OmegaMeromorphicZeroPropagationAPI`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
A zero germ and a nonzero germ cannot coexist at a point where `H` is meromorphic.
-/
theorem zero_germ_not_nonzero_germ_at
    {H : ℂ → ℂ}
    {z : ℂ}
    (hHz : MeromorphicAt H z)
    (hzero : H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0))
    (hnonzero : ∀ᶠ w in 𝓝[≠] z, H w ≠ 0) :
    False := by
  have hfreq :
      ∃ᶠ w in 𝓝[≠] z, H w = 0 :=
    (hHz.frequently_zero_iff_eventuallyEq_zero).2 hzero

  exact hfreq (by
    filter_upwards [hnonzero] with w hw hzero_w
    exact hw hzero_w)

/--
If a meromorphic function on `Ω` has a zero germ at one point of `Ω`, then it has
a zero germ at every point of `Ω`.
-/
theorem meromorphic_zero_germ_propagates_to_all_Omega
    (H : ℂ → ℂ)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ Ω)
    (hH : MeromorphicOnC H Ω)
    (hlocal : H =ᶠ[𝓝[≠] z₀] (fun _ : ℂ => 0)) :
    ∀ z : ℂ, z ∈ Ω →
      H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0) := by
  let A : Set ℂ :=
    {z : ℂ | H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0)}

  let B : Set ℂ :=
    {z : ℂ | ∀ᶠ w in 𝓝[≠] z, H w ≠ 0}

  have hAopen : IsOpen A := by
    simpa [A] using isOpen_zeroGermSet H

  have hBopen : IsOpen B := by
    simpa [B] using isOpen_nonzeroGermSet H

  have hcover : Ω ⊆ A ∪ B := by
    intro z hz
    rcases meromorphic_zero_or_nonzero_germ_at H hH hz with hzero | hnonzero
    · exact Or.inl hzero
    · exact Or.inr hnonzero

  have hAne : (Ω ∩ A).Nonempty := by
    exact ⟨z₀, hz₀, hlocal⟩

  have hA_inter_B_empty :
      ∀ z : ℂ, z ∈ Ω → z ∈ A → z ∈ B → False := by
    intro z hz hAz hBz
    exact
      zero_germ_not_nonzero_germ_at
        (hH z hz)
        hAz
        hBz

  by_contra hnot
  push_neg at hnot

  rcases hnot with ⟨z₁, hz₁Ω, hz₁notA⟩

  have hz₁B : z₁ ∈ B := by
    have hz₁AB : z₁ ∈ A ∪ B := hcover hz₁Ω
    rcases hz₁AB with hA | hB
    · exact False.elim (hz₁notA hA)
    · exact hB

  have hBne : (Ω ∩ B).Nonempty := by
    exact ⟨z₁, hz₁Ω, hz₁B⟩

  have hInter :
      (Ω ∩ (A ∩ B)).Nonempty :=
    isPreconnected_Omega_native
      A
      B
      hAopen
      hBopen
      hcover
      hAne
      hBne

  rcases hInter with ⟨w, hwΩ, hwAB⟩
  exact hA_inter_B_empty w hwΩ hwAB.1 hwAB.2

/--
Theorem-backed implementation of `OmegaMeromorphicZeroPropagationAPI`.
-/
def defaultOmegaMeromorphicZeroPropagationAPI :
    OmegaMeromorphicZeroPropagationAPI :=
  { h_zero_propagate := fun H z₀ hz₀ hH hlocal =>
      eventuallyEq_zero_codiscreteWithin_of_forall_nhdsNE
        H
        (meromorphic_zero_germ_propagates_to_all_Omega
          H
          z₀
          hz₀
          hH
          hlocal) }

/--
Endpoint after discharging the Appendix-F zero-propagation input.

Remaining explicit inputs are now exactly:
* `ZF`;
* `Y`;
* `X`;
* `E`.
-/
theorem finalRHSpine_after_zeroPropagation
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI) :
    RiemannHypothesis :=
  finalZeroPropagationRHSpine
    ZF
    Y
    X
    E
    defaultOmegaMeromorphicZeroPropagationAPI

end

end RHFormalization
