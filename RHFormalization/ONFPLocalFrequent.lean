import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Analytic.IsolatedZeros
import RHFormalization.FinalConditionalSpine

/-!
# RHFormalization.ONFPLocalFrequent

First local helper toward `OmegaNormalFormCodiscretePropagationAPI`.

If two functions agree along `Filter.codiscreteWithin V`, and `z₀ ∈ V` with `V`
open, then they agree on a punctured neighbourhood of `z₀`.

This is the bridge from codiscrete overlap equality to the local frequent/eventual
equality input used by analytic identity theorems.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Codiscrete equality on an open set gives punctured-neighbourhood equality at any
point of that open set.
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_of_mem_open
    {F G : ℂ → ℂ}
    {V : Set ℂ}
    {z₀ : ℂ}
    (hVopen : IsOpen V)
    (hz₀ : z₀ ∈ V)
    (hcod : F =ᶠ[Filter.codiscreteWithin V] G) :
    F =ᶠ[𝓝[≠] z₀] G := by
  have hSet :
      {z : ℂ | F z = G z} ∈ Filter.codiscreteWithin V := hcod

  have hUnion :
      {z : ℂ | F z = G z} ∪ Vᶜ ∈ 𝓝[≠] z₀ := by
    exact
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hSet)
        z₀
        hz₀

  have hV_nhdsNE :
      V ∈ 𝓝[≠] z₀ := by
    exact
      (nhdsWithin_le_nhds : 𝓝[≠] z₀ ≤ 𝓝 z₀)
        (hVopen.mem_nhds hz₀)

  filter_upwards [hUnion, hV_nhdsNE] with z hzUnion hzV
  rcases hzUnion with hEq | hzNotV
  · exact hEq
  · exact False.elim (hzNotV hzV)

/--
Codiscrete equality on an open set gives frequent punctured equality at any point
of that open set.
-/
theorem frequently_eq_nhdsNE_of_eventuallyEq_codiscreteWithin_of_mem_open
    {F G : ℂ → ℂ}
    {V : Set ℂ}
    {z₀ : ℂ}
    (hVopen : IsOpen V)
    (hz₀ : z₀ ∈ V)
    (hcod : F =ᶠ[Filter.codiscreteWithin V] G) :
    ∃ᶠ z in 𝓝[≠] z₀, F z = G z := by
  exact
    (eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_of_mem_open
      hVopen
      hz₀
      hcod).frequently

end

end RHFormalization
