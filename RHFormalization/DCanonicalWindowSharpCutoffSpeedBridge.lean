import RHFormalization.DCanonicalWindowSharpCutoffScalar

/-!
# RHFormalization.DCanonicalWindowSharpCutoffSpeedBridge

Bridge from the scalar sharp-cutoff estimate to an inverse-speed estimate.

This is not another package wrapper.

It converts the scalar D.CANONICAL-WINDOW algebra

  |G a * ((2L - |a|)/(2L)) - G a| ≤ Gbound * R/(2L)

into the exact metric form needed for the compact-speed API:

  dist (gbar n a) (G a) ≤ 1 / speed n.

The next file after this should instantiate `gbar` as `W.gbar_stage (alpha n)`,
`G` as `W.G_limit`, and `L` as the sharp cutoff length.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Sharp-cutoff scalar formula implies an inverse-speed distance estimate.

This is the direct bridge from the scalar overlap computation to the
`DCanonicalWindowCompactSpeedAPI.h_compact_window_speed_rate` shape.
-/
theorem sharpCutoff_dist_le_invSpeed_of_formula
    (gbar : ℕ → ℝ → ℝ)
    (G : ℝ → ℝ)
    (L speed : ℕ → ℝ)
    (Gbound R : ℝ)
    (n : ℕ)
    (a : ℝ)
    (hL : 0 < L n)
    (hR : 0 ≤ R)
    (hGbound_nonneg : 0 ≤ Gbound)
    (ha : |a| ≤ R)
    (hG_bound : ∀ x : ℝ, |x| ≤ R → |G x| ≤ Gbound)
    (hformula :
      gbar n a =
        G a * ((2 * L n - |a|) / (2 * L n)))
    (hbudget :
      Gbound * (R / (2 * L n)) ≤ (1 : ℝ) / speed n) :
    dist (gbar n a) (G a) ≤ (1 : ℝ) / speed n := by
  rw [Real.dist_eq]
  have hscalar :
      |G a * ((2 * L n - |a|) / (2 * L n)) - G a|
        ≤ Gbound * (R / (2 * L n)) :=
    sharpCutoff_normalized_kernel_error_le
      G
      Gbound
      (L n)
      R
      a
      hL
      hR
      hGbound_nonneg
      ha
      hG_bound
  have hrewrite :
      |gbar n a - G a|
        =
      |G a * ((2 * L n - |a|) / (2 * L n)) - G a| := by
    rw [hformula]
  rw [hrewrite]
  exact le_trans hscalar hbudget

end

end RHFormalization
