import RHFormalization.DefaultDenominatorSimpleZeroOrder

/-!
# RHFormalization.PuncturedIdentityLocalCore

Mathlib-native punctured identity core for the Appendix-F meromorphic step.

The old `MeromorphicIdentityPrincipleAPI` gives pointwise equality on all of Ω.
For meromorphic functions, Mathlib's natural equality notion is codiscrete /
punctured-neighbourhood equality.

This file introduces the punctured identity API and proves the local pole obstruction
from punctured equality directly.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Punctured-neighbourhood equality at a point.
-/
abbrev PuncturedEqAtC
    (f g : ℂ → ℂ)
    (z : ℂ) : Prop :=
  f =ᶠ[𝓝[≠] z] g

/--
Meromorphic identity principle in the punctured form actually needed by the
local pole contradiction.

Given equality on the nonempty overlap and meromorphicity on `U`, it returns
punctured equality near a chosen point `z ∈ U`.
-/
structure PuncturedMeromorphicIdentityAPI where
  h_punctured_identity :
    ∀ (f g : ℂ → ℂ) (U V : Set ℂ) (z : ℂ),
      IsPreconnected U →
      IsOpen V →
      V.Nonempty →
      V ⊆ U →
      z ∈ U →
      MeromorphicOnC f U →
      MeromorphicOnC g U →
      Set.EqOn f g V →
      PuncturedEqAtC f g z

/--
Punctured version of the local holomorphic-balance obstruction.

If

`F = G - Z`

on a punctured neighbourhood of `z`, and `F` and `G` are holomorphic at `z`,
then `Z` cannot have negative meromorphic order at `z`.
-/
theorem local_order_obstruction_from_punctured_holomorphic_balance
    (F G Z : ℂ → ℂ)
    (z : ℂ)
    (hpunct :
      PuncturedEqAtC F (fun s => G s - Z s) z)
    (hF : HolomorphicAtC F z)
    (hG : HolomorphicAtC G z)
    (hZneg : meromorphicOrderAt Z z < 0) :
    False := by
  have hZeq_punct :
      Z =ᶠ[𝓝[≠] z] (fun s => G s - F s) := by
    filter_upwards [hpunct] with w hw
    have hcalc : Z w = G w - F w := by
      rw [hw]
      ring
    exact hcalc

  have hdiff_holo :
      HolomorphicAtC (fun s => G s - F s) z :=
    hG.sub hF

  have hdiff_nonneg :
      0 ≤ meromorphicOrderAt (fun s => G s - F s) z :=
    hdiff_holo.meromorphicOrderAt_nonneg

  have horder_eq :
      meromorphicOrderAt Z z =
        meromorphicOrderAt (fun s => G s - F s) z := by
    exact meromorphicOrderAt_congr hZeq_punct

  have hZneg_diff :
      meromorphicOrderAt (fun s => G s - F s) z < 0 := by
    simpa [horder_eq] using hZneg

  exact not_lt_of_ge hdiff_nonneg hZneg_diff

end

end RHFormalization
