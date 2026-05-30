import Mathlib
import RHFormalization.PrincipalPartCoboundedSplit

/-!
# RHFormalization.DefaultCoboundedAddFiniteLimit

Discharges `CoboundedAddFiniteLimitAPI`.

If `f` tends to the cobounded filter and `g` tends to a finite value `c`, then
`f + g` also tends to the cobounded filter.

This is the bounded-perturbation lemma needed in the local simple-pole argument.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Bornology
open scoped Pointwise

/--
A function is eventually bounded along a filter if its values are eventually
contained in a bounded set.
-/
def EventuallyBoundedOnFilter
    (g : ℂ → ℂ)
    (l : Filter ℂ) : Prop :=
  ∃ B : Set ℂ,
    Bornology.IsBounded B ∧
      ∀ᶠ w in l, g w ∈ B

/--
A finite limit implies eventual boundedness along the filter.
-/
theorem eventuallyBounded_of_tendsto_nhds
    {g : ℂ → ℂ}
    {l : Filter ℂ}
    {c : ℂ}
    (hg : Tendsto g l (𝓝 c)) :
    EventuallyBoundedOnFilter g l := by
  refine ⟨Metric.ball c 1, ?_, ?_⟩
  · rw [Metric.isBounded_iff]
    refine ⟨2, ?_⟩
    intro x hx y hy
    have hx' : dist x c < 1 := hx
    have hy' : dist y c < 1 := hy
    have htri : dist x y ≤ dist x c + dist c y := dist_triangle x c y
    have hcy : dist c y = dist y c := dist_comm c y
    have hsum : dist x c + dist c y < 2 := by
      rw [hcy]
      linarith
    exact le_of_lt (lt_of_le_of_lt htri hsum)
  · have hg_map : Metric.ball c 1 ∈ Filter.map g l :=
      hg (Metric.ball_mem_nhds c zero_lt_one)
    rw [mem_map] at hg_map
    exact hg_map

/--
Adding an eventually bounded perturbation to a cobounded function preserves
coboundedness.
-/
theorem tendsto_add_cobounded_of_eventuallyBounded
    {f g : ℂ → ℂ}
    {l : Filter ℂ}
    (hf : Tendsto f l (Bornology.cobounded ℂ))
    (hgB : EventuallyBoundedOnFilter g l) :
    Tendsto (fun w : ℂ => f w + g w) l (Bornology.cobounded ℂ) := by
  intro S hS
  rw [mem_map]

  have hScomp : Bornology.IsBounded (Sᶜ) := by
    rw [Bornology.isBounded_def]
    simpa using hS

  rcases hgB with ⟨B, hB, hgEv⟩

  have hBad : Bornology.IsBounded (Sᶜ - B) :=
    hScomp.sub hB

  have hAvoidTarget : (Sᶜ - B)ᶜ ∈ Bornology.cobounded ℂ := by
    rw [← Bornology.isBounded_def]
    exact hBad

  have hfEv_map : (Sᶜ - B)ᶜ ∈ Filter.map f l :=
    hf hAvoidTarget
  rw [mem_map] at hfEv_map

  filter_upwards [hfEv_map, hgEv] with w hf_not_bad hg_mem
  by_contra hnotS

  have hsum_bad : f w + g w ∈ Sᶜ := by
    exact hnotS

  have hf_bad : f w ∈ Sᶜ - B := by
    refine ⟨f w + g w, hsum_bad, g w, hg_mem, ?_⟩
    ring

  exact hf_not_bad hf_bad

/--
Cobounded plus finite-limit perturbation preserves coboundedness.
-/
theorem tendsto_add_cobounded_of_finite_limit
    (f g : ℂ → ℂ)
    (l : Filter ℂ)
    (c : ℂ)
    (hf : Tendsto f l (Bornology.cobounded ℂ))
    (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun w : ℂ => f w + g w) l (Bornology.cobounded ℂ) :=
  tendsto_add_cobounded_of_eventuallyBounded
    hf
    (eventuallyBounded_of_tendsto_nhds hg)

/--
Default theorem-backed implementation of `CoboundedAddFiniteLimitAPI`.
-/
def defaultCoboundedAddFiniteLimitAPI :
    CoboundedAddFiniteLimitAPI :=
  { h_add_finite_limit :=
      tendsto_add_cobounded_of_finite_limit }

/--
Endpoint after discharging `CoboundedAddFiniteLimitAPI`.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_splitCobounded`,
this theorem no longer requires:

`BA : CoboundedAddFiniteLimitAPI`.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleOnly
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (SP : SimplePoleCoboundedAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_splitCobounded
    ZF
    Y
    X
    E
    I
    SP
    defaultCoboundedAddFiniteLimitAPI

end

end RHFormalization
