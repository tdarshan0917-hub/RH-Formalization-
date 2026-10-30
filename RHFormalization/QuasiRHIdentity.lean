import RHFormalization.QuasiRHConnected
import RHFormalization.DefaultOmegaCodiscreteIdentity
import RHFormalization.DefaultOmegaPreperfect
import Mathlib

/-!
# QuasiRHIdentity — QR-3: the meromorphic identity principle on any open preconnected U

The banked Ω proof (`omega_codiscrete_identity_native`) uses only that Ω is preconnected,
and the punctured upgrade only that Ω is open (preperfect). Restated for a general open
preconnected `U`, then specialized to `Ω_θ` via QR-2.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter Set Topology

/-- Codiscrete identity principle on a preconnected `U`. -/
theorem codiscrete_identity_of_preconnected
    (f g : ℂ → ℂ) (U V : Set ℂ) (hUc : IsPreconnected U)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVsub : V ⊆ U)
    (hf : MeromorphicOnC f U) (hg : MeromorphicOnC g U)
    (hEq : Set.EqOn f g V) :
    f =ᶠ[Filter.codiscreteWithin U] g := by
  have hsub : MeromorphicOn (f - g) U := hf.sub hg
  obtain ⟨x₀, hx₀⟩ := hVne
  have hx₀U : x₀ ∈ U := hVsub hx₀
  have h0 : (f - g) =ᶠ[𝓝[≠] x₀] 0 := by
    filter_upwards [nhdsWithin_le_nhds (hVopen.mem_nhds hx₀)] with z hz
    simp [Pi.sub_apply, hEq hz]
  have htop : meromorphicOrderAt (f - g) x₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 h0
  have hall : ∀ y, y ∈ U → meromorphicOrderAt (f - g) y = ⊤ := by
    intro y hy
    by_contra hne
    exact (hsub.meromorphicOrderAt_ne_top_of_isPreconnected hUc hy hx₀U hne) htop
  have hmem : {z | f z = g z} ∈ Filter.codiscreteWithin U := by
    rw [mem_codiscreteWithin]
    intro x hx
    rw [Filter.disjoint_principal_right]
    have hx0 : (f - g) =ᶠ[𝓝[≠] x] 0 := meromorphicOrderAt_eq_top_iff.1 (hall x hx)
    filter_upwards [hx0] with z hz
    have hz' : f z = g z := by
      have h : f z - g z = 0 := by simpa [Pi.sub_apply] using hz
      exact sub_eq_zero.mp h
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
    exact fun _ => hz'
  exact Filter.eventuallyEq_of_mem hmem (fun z hz => hz)

/-- Punctured identity principle on an open preconnected `U`. -/
theorem punctured_identity_of_preconnected
    (f g : ℂ → ℂ) (U V : Set ℂ) (z : ℂ)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVsub : V ⊆ U) (hz : z ∈ U)
    (hf : MeromorphicOnC f U) (hg : MeromorphicOnC g U)
    (hEq : Set.EqOn f g V) :
    PuncturedEqAtC f g z :=
  MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf z hz) (hg z hz) hz hUo.preperfect
    (codiscrete_identity_of_preconnected f g U V hUc hVopen hVne hVsub hf hg hEq)

/-- **QR-3**: the punctured identity principle on `Ω_θ` (θ ≥ 0). -/
theorem punctured_identity_OmegaTheta
    (θ : ℝ) (hθ : 0 ≤ θ)
    (f g : ℂ → ℂ) (V : Set ℂ) (z : ℂ)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVsub : V ⊆ OmegaTheta θ)
    (hz : z ∈ OmegaTheta θ)
    (hf : MeromorphicOnC f (OmegaTheta θ)) (hg : MeromorphicOnC g (OmegaTheta θ))
    (hEq : Set.EqOn f g V) :
    PuncturedEqAtC f g z :=
  punctured_identity_of_preconnected f g (OmegaTheta θ) V z
    (isOpen_OmegaTheta θ) (isPreconnected_OmegaTheta θ hθ)
    hVopen hVne hVsub hz hf hg hEq

#print axioms codiscrete_identity_of_preconnected
#print axioms punctured_identity_of_preconnected
#print axioms punctured_identity_OmegaTheta

end

end RHFormalization
