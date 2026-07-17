import RHFormalization.AnalyticWrappers

/-!
# Principal-part transfer under eventual equality

If `f = g` on a punctured neighborhood of `z`, then `f` and `g` have the same
principal part at `z`. This lets us transport the model's principal part to the
tsum Bshared, once they are shown to agree near the witness via analytic
continuation.
-/

namespace RHFormalization

open Filter Topology

/-- Principal parts transfer under punctured-neighborhood equality. -/
theorem hasPrincipalPart_of_eventuallyEq
    {f g : ℂ → ℂ} {z c : ℂ}
    (hfg : ∀ᶠ w in 𝓝 z, w ≠ z → f w = g w)
    (hg : HasPrincipalPartAtC g z c) :
    HasPrincipalPartAtC f z c := by
  obtain ⟨h, hh_an, hh_eq⟩ := hg
  refine ⟨h, hh_an, ?_⟩
  filter_upwards [hfg, hh_eq] with w hfgw hgw
  intro hwz
  rw [hfgw hwz]
  exact hgw hwz

end RHFormalization
