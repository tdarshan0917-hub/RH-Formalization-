import RHFormalization.ZpoleFromSeries
import Mathlib.Analysis.PSeries
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Bases
import RHFormalization.DefaultZeroMultiplicity
import Mathlib.Analysis.Meromorphic.Order

/-!
# RHFormalization.ZetaZeroCounting

Foundation for the `hsum` input (zero-density summability). This file is the START of
a separate, multi-stage formalization: proving

  Summable (fun ρ : {ρ // IsNontrivialZetaZero ρ} => (mult ρ : ℝ) / (1 + ρ.im ^ 2))

The classical proof rests on the **Riemann–von Mangoldt counting bound**
`N(T) = O(T log T)`, which is NOT in Mathlib and is the genuine open formalization target.

STRATEGY:
* `ZetaCountingBound` — the hard pillar (RvM), stated as an explicit Prop. OPEN PROBLEM.
* downstream: `ZetaCountingBound → hsum`, via dyadic-shell comparison.

This file edits NOTHING else. It is isolated from the eta track and the H-side track.
-/

namespace RHFormalization

open Filter Topology TopologicalSpace
open scoped BigOperators

/-- The nonnegative zero-density summand we must show is summable. -/
noncomputable def zeroDensitySummand
    (M : ZeroMultiplicityData) (ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}) : ℝ :=
  (M.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)

/-- The summand is nonnegative (ℕ-valued multiplicity over a positive denominator). -/
theorem zeroDensitySummand_nonneg
    (M : ZeroMultiplicityData) (ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}) :
    0 ≤ zeroDensitySummand M ρ := by
  unfold zeroDensitySummand
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · positivity

/-- Comparison wrapper: if the zero-density summand is dominated by a summable
nonnegative function, it is summable. (Specialization of `Summable.of_nonneg_of_le`.) -/
theorem zeroDensity_summable_of_le
    (M : ZeroMultiplicityData)
    (g : {ρ : ℂ // IsNontrivialZetaZero ρ} → ℝ)
    (hg : Summable g)
    (hle : ∀ ρ, zeroDensitySummand M ρ ≤ g ρ) :
    Summable (zeroDensitySummand M) :=
  Summable.of_nonneg_of_le (zeroDensitySummand_nonneg M) hle hg

#print axioms zeroDensity_summable_of_le

/-!
## The two open pillars

`hsum` classically rests on:
1. **Countability** of the nontrivial zero set (local isolation + σ-compact strip).
2. **Riemann–von Mangoldt** counting bound `N(T) = O(T log T)`.

We bundle exactly what these provide into one hypothesis `ZetaZeroDensityData`, then prove
`hsum` follows. The bundle is the honest interface: an enumeration of the zeros (countability)
together with summability of the enumerated density (the counting bound, post dyadic-shell sum).
Both pillars remain OPEN as standalone formalization targets; this file proves the reduction
from them to `hsum`.
-/

/-- The classical zero-density input, bundled. `enum` is an injection of the nontrivial zeros
into ℕ (countability); `hsummable` is summability of the density pulled back along `enum`
(this is what the Riemann–von Mangoldt bound classically delivers via dyadic shells). -/
structure ZetaZeroDensityData (M : ZeroMultiplicityData) where
  enum : {ρ : ℂ // IsNontrivialZetaZero ρ} → ℕ
  enum_injective : Function.Injective enum
  hsummable : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
    zeroDensitySummand M ρ)

/-- **Reduction**: the bundled zero-density data immediately yields `hsum`.
(This is trivial once `hsummable` is in the bundle — the content is that the bundle is
exactly the right interface. The hard work is *producing* a `ZetaZeroDensityData`, which
needs the two open pillars.) -/
theorem hsum_of_zeroDensityData
    (M : ZeroMultiplicityData) (D : ZetaZeroDensityData M) :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (M.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) :=
  D.hsummable

#print axioms hsum_of_zeroDensityData

/-!
## Pillar 1 (countability) — being built here

Chain: ζ meromorphic on the strip ⟹ its zero set is codiscrete ⟹ discrete subspace ⟹
(second-countable subspace ⟹ separable ⟹) countable. Every link is in Mathlib; we assemble.
-/

/-- **Topology core (ζ-free, reusable):** a set with discrete subspace topology inside a
second-countable space is countable. Discrete subspace ⟹ second-countable subspace ⟹ separable
⟹ (since discrete) countable. -/
theorem countable_of_isDiscrete_subtype
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] (s : Set X)
    (hs : DiscreteTopology s) : s.Countable := by
  -- s as a subtype is second-countable (Subtype.secondCountableTopology) and discrete (hs),
  -- hence separable, hence (discrete + separable) countable.
  have hsep : SeparableSpace s := SecondCountableTopology.to_separableSpace
  have hcount : Countable s := (separableSpace_iff_countable).mp hsep
  exact Set.countable_coe_iff.mp hcount

#print axioms countable_of_isDiscrete_subtype

/-- The open half-plane `{re < 1}`, ζ's analytic domain (omits the pole at 1). -/
def zetaStripDomain : Set ℂ := {s : ℂ | s.re < 1}

/-- **Pillar 1 main result:** the nontrivial zeros of ζ form a countable set.
ζ analytic on `{re<1}` ⟹ meromorphic ⟹ (codiscrete order-zero-or-top set; never ⊤ since
not locally zero) ⟹ zeros are discrete ⟹ countable. -/
theorem nontrivialZeros_countable :
    {ρ : ℂ | IsNontrivialZetaZero ρ}.Countable := by
  -- Work on the open analytic domain U = {re < 1}.
  set U : Set ℂ := {s : ℂ | s.re < 1} with hU
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hMero : MeromorphicOn riemannZeta U :=
    zeta_analyticOnNhd_re_lt_one.meromorphicOn
  -- Order is never ⊤ on U (ζ is not locally zero there).
  have hNeTop : ∀ u ∈ U, meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    intro u hu htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hA : AnalyticAt ℂ riemannZeta u := zeta_analyticOnNhd_re_lt_one u hu
    rcases hA.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · -- ζ = 0 on a full punctured→full nbhd ⟹ contradiction with not-locally-zero
      exact zeta_not_locally_zero u hu h0
    · -- ζ ≠ 0 eventually on 𝓝[≠] u contradicts htop (ζ = 0 eventually there)
      have : ∀ᶠ z in nhdsWithin u {u}ᶜ, (riemannZeta z = 0 ∧ riemannZeta z ≠ 0) :=
        htop.and hne
      rcases this.exists with ⟨z, hz0, hzne⟩
      exact hzne hz0
  -- The codiscrete order-zero-or-top set, within U.
  have hcod := hMero.codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top hNeTop
  -- Identify that set with the NONZEROS of ζ in U: {u∈U | ζ u ≠ 0}.
  have hset : {u | u ∈ U ∧ (meromorphicOrderAt riemannZeta u = 0 ∨
      meromorphicOrderAt riemannZeta u = ⊤)} = {u | u ∈ U ∧ riemannZeta u ≠ 0} := by
    ext u
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨huU, hor⟩
      refine ⟨huU, ?_⟩
      have hA : AnalyticAt ℂ riemannZeta u := zeta_analyticOnNhd_re_lt_one u huU
      rcases hor with h0 | htop
      · -- order 0 ⟹ ζ ≠ 0
        rw [hA.meromorphicOrderAt_eq] at h0
        have hz0 : analyticOrderAt riemannZeta u = 0 := by
          cases hc : analyticOrderAt riemannZeta u with
          | top => rw [hc] at h0; simp at h0
          | coe n =>
            rw [hc] at h0
            simp only [ENat.map_coe] at h0
            exact_mod_cast h0
        exact (hA.analyticOrderAt_eq_zero).1 hz0
      · exact absurd htop (hNeTop u huU)
    · rintro ⟨huU, hne⟩
      refine ⟨huU, Or.inl ?_⟩
      have hA : AnalyticAt ℂ riemannZeta u := zeta_analyticOnNhd_re_lt_one u huU
      rw [hA.meromorphicOrderAt_eq]
      have : analyticOrderAt riemannZeta u = 0 := (hA.analyticOrderAt_eq_zero).2 hne
      simp [this]
  rw [hset] at hcod
  -- Now {ζ≠0}∩U is codiscrete-complement-style: its complement-zeros are discrete.
  -- Let Z = {ζ = 0} ∩ U.  hcod says {ζ≠0 in U} ∈ codiscreteWithin U, i.e. Zᶜ ⊇ that set.
  -- We need Zᶜ ∈ codiscreteWithin U.  Since {u∈U | ζ u≠0} ⊆ Zᶜ, upward closure gives it.
  set Z : Set ℂ := {u | riemannZeta u = 0} with hZ
  have hsub : {u | u ∈ U ∧ riemannZeta u ≠ 0} ⊆ Zᶜ := by
    intro u hu; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hZ]; exact hu.2
  have hZc : Zᶜ ∈ Filter.codiscreteWithin U := Filter.mem_of_superset hcod hsub
  have hdisc : IsDiscrete (Z ∩ U) := isDiscrete_of_codiscreteWithin hZc
  -- IsDiscrete ⟹ DiscreteTopology ⟹ countable.
  have hDT : DiscreteTopology (Z ∩ U : Set ℂ) := by
    rwa [← isDiscrete_iff_discreteTopology]
  have hZUcount : (Z ∩ U).Countable := countable_of_isDiscrete_subtype _ hDT
  -- Nontrivial zeros ⊆ Z ∩ U.
  refine Set.Countable.mono ?_ hZUcount
  intro ρ hρ
  obtain ⟨hz, h0, h1⟩ := hρ
  exact ⟨hz, h1⟩

#print axioms nontrivialZeros_countable

/-!
## Pillar 1 → enum, and the shell→summable reduction

Countability (`nontrivialZeros_countable`) gives an injective `enum` of the zeros into ℕ.
The reduction below says: if the density pulled back along an injective enum is dominated by a
summable ℕ-sequence, then the density is summable (= `hsummable`). The existence of such a
dominating sequence is exactly what the counting bound (pillar 2) classically supplies.
-/

/-- The nontrivial zeros admit an injective enumeration into ℕ (from countability). -/
theorem exists_zero_enum :
    ∃ e : {ρ : ℂ // IsNontrivialZetaZero ρ} → ℕ, Function.Injective e := by
  haveI : Countable {ρ : ℂ // IsNontrivialZetaZero ρ} :=
    nontrivialZeros_countable.to_subtype
  exact Countable.exists_injective_nat _

#print axioms exists_zero_enum

/-- **Shell→summable reduction.** If an injective enum `e` of the zeros pulls the density back
into a function dominated (pointwise) by a summable nonnegative ℕ-sequence `b`, then the density
is summable. This is the bridge that turns the counting bound into `hsummable`. -/
theorem summable_density_of_enum_dominated
    (M : ZeroMultiplicityData)
    (e : {ρ : ℂ // IsNontrivialZetaZero ρ} → ℕ) (he : Function.Injective e)
    (b : ℕ → ℝ) (hb : Summable b)
    (hdom : ∀ ρ, zeroDensitySummand M ρ ≤ b (e ρ)) :
    Summable (zeroDensitySummand M) := by
  -- b ∘ e is summable (pull a summable ℕ-sequence back along the injection e).
  have hbe : Summable (fun ρ => b (e ρ)) := hb.comp_injective he
  -- density ≤ b∘e, density ≥ 0 ⟹ density summable by comparison.
  exact zeroDensity_summable_of_le M (fun ρ => b (e ρ)) hbe hdom

#print axioms summable_density_of_enum_dominated

end RHFormalization
