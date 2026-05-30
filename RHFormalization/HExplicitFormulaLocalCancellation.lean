import RHFormalization.HExplicitFormulaHolomorphyLocal

/-!
# RHFormalization.HExplicitFormulaLocalCancellation

Local principal-part cancellation for the H/E explicit-formula holomorphy target.

After `HExplicitFormulaHolomorphyLocal`, the current frontier is:

  ∀ z ∈ Ω,
    ∃ h, HolomorphicAtC h z ∧
      LocalEqAtC h (fun s => Y.B.Cshared.Bshared s + Zpole s) z.

This file proves the basic local cancellation lemma needed at a pole:
opposite simple principal parts cancel, provided the total function has the
correct value at the pole.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Convert punctured-neighborhood equality plus equality at the center into
ordinary local equality.

This is needed because `HasPrincipalPartAtC` only gives equality for `w ≠ z`,
while `LocalEqAtC` is equality in the full neighborhood filter.
-/
theorem localEqAtC_of_punctured_eventuallyEq_and_point_eq
    {f h : ℂ → ℂ}
    {z : ℂ}
    (hpunct : ∀ᶠ w in 𝓝 z, w ≠ z → h w = f w)
    (hpoint : h z = f z) :
    LocalEqAtC h f z := by
  filter_upwards [hpunct] with w hw
  by_cases hwz : w = z
  · subst w
    exact hpoint
  · exact hw hwz

/--
Local holomorphic extension from cancellation of opposite simple principal parts.

Here `f` and `g` are the two meromorphic pieces, with principal parts
`c/(w-z)` and `(-c)/(w-z)`.  The holomorphic local extension is `hF + hG`.

The extra point-value hypothesis is essential because principal-part data only
controls the punctured neighborhood.
-/
theorem local_holomorphic_extension_add_of_cancelled_principal_parts
    (f g hF hG : ℂ → ℂ)
    (z c : ℂ)
    (hhF : HolomorphicAtC hF z)
    (hhG : HolomorphicAtC hG z)
    (hf :
      ∀ᶠ w in 𝓝 z,
        w ≠ z → f w = c / (w - z) + hF w)
    (hg :
      ∀ᶠ w in 𝓝 z,
        w ≠ z → g w = (-c) / (w - z) + hG w)
    (hpoint :
      hF z + hG z = f z + g z) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h z ∧
        LocalEqAtC h (fun w : ℂ => f w + g w) z := by
  refine ⟨fun w : ℂ => hF w + hG w, ?_, ?_⟩
  · exact hhF.add hhG
  · apply localEqAtC_of_punctured_eventuallyEq_and_point_eq
    · filter_upwards [hf, hg] with w hfw hgw hwz
      have hf_eq : f w = c / (w - z) + hF w := hfw hwz
      have hg_eq : g w = (-c) / (w - z) + hG w := hgw hwz
      calc
        hF w + hG w
            = (c / (w - z) + hF w) + ((-c) / (w - z) + hG w) := by
                ring
        _ = f w + g w := by
                rw [← hf_eq, ← hg_eq]
    · exact hpoint

end

end RHFormalization
