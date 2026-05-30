import RHFormalization.FinalZeroPropagationSpine
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Meromorphic.Order

/-!
# RHFormalization.OmegaMeromorphicZeroPropagationProof

Real proof work toward `OmegaMeromorphicZeroPropagationAPI`.

No new RH endpoint is introduced here.  This file begins the proof of the remaining
Appendix-F zero-propagation theorem.

Current target:

If `H` is meromorphic on `Ω` and is zero on one punctured neighbourhood, then
`H` is zero on a codiscrete subset of `Ω`.

The theorem below proves the final codiscrete step from pointwise zero-germ
propagation.  The remaining hard lemma is the actual propagation of the zero germ
across preconnected `Ω`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Local meromorphic zero dichotomy at a point of `Ω`.

A meromorphic function is either eventually zero on the punctured neighbourhood,
or eventually nonzero there.
-/
theorem meromorphic_zero_or_nonzero_germ_at
    (H : ℂ → ℂ)
    {z : ℂ}
    (hH : MeromorphicOnC H Ω)
    (hz : z ∈ Ω) :
    (H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0)) ∨
      (∀ᶠ w in 𝓝[≠] z, H w ≠ 0) := by
  exact (hH z hz).eventually_eq_zero_or_eventually_ne_zero

/--
If a function is eventually zero on the punctured neighbourhood of every point
of `Ω`, then it is zero along `Filter.codiscreteWithin Ω`.

This is the codiscrete endgame of `OmegaMeromorphicZeroPropagationAPI`.
-/
theorem eventuallyEq_zero_codiscreteWithin_of_forall_nhdsNE
    (H : ℂ → ℂ)
    (hall :
      ∀ z : ℂ,
        z ∈ Ω →
          H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0)) :
    H =ᶠ[Filter.codiscreteWithin Ω] (fun _ : ℂ => 0) := by
  have hzeroSet :
      {z : ℂ | H z = 0} ∈ Filter.codiscreteWithin Ω := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro z hz
    have hzlocal :
        {w : ℂ | H w = 0} ∈ 𝓝[≠] z := by
      simpa [Filter.EventuallyEq] using hall z hz
    exact Filter.mem_of_superset hzlocal (by
      intro w hw
      exact Or.inl hw)
  simpa [Filter.EventuallyEq] using hzeroSet

/-
The next real theorem to prove is:

theorem meromorphic_zero_germ_propagates_to_all_Omega
    (H : ℂ → ℂ)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ Ω)
    (hH : MeromorphicOnC H Ω)
    (hlocal : H =ᶠ[𝓝[≠] z₀] (fun _ : ℂ => 0)) :
    ∀ z : ℂ, z ∈ Ω →
      H =ᶠ[𝓝[≠] z] (fun _ : ℂ => 0)

This is the actual Appendix-F zero-germ propagation step.
Once it is proved, `OmegaMeromorphicZeroPropagationAPI` follows immediately from
`eventuallyEq_zero_codiscreteWithin_of_forall_nhdsNE`.
-/

end

end RHFormalization
