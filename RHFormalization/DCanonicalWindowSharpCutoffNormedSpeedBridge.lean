import RHFormalization.DCanonicalWindowSharpCutoffScalar

/-!
# RHFormalization.DCanonicalWindowSharpCutoffNormedSpeedBridge

Normed-space version of the sharp-cutoff inverse-speed bridge.

The earlier bridge was real-valued.  The actual D-window API has
`gbar_stage` and `G_limit` valued in `ℂ`, so the correct formal shape is a
real scalar multiple of a normed-space vector:

  gbar n a = r • G a

with

  r = (2L - |a|)/(2L).

This file proves the metric estimate in any real normed vector space, hence in
`ℂ`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Sharp-cutoff scalar formula implies an inverse-speed distance estimate in any
real normed vector space.

This is the correct bridge for the actual D-window API, where the window values
are complex.
-/
theorem sharpCutoff_dist_le_invSpeed_of_smul_formula
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (gbar : ℕ → ℝ → E)
    (G : ℝ → E)
    (L speed : ℕ → ℝ)
    (Gbound R : ℝ)
    (n : ℕ)
    (a : ℝ)
    (hL : 0 < L n)
    (hR : 0 ≤ R)
    (hGbound_nonneg : 0 ≤ Gbound)
    (ha : |a| ≤ R)
    (hG_bound : ∀ x : ℝ, |x| ≤ R → ‖G x‖ ≤ Gbound)
    (hformula :
      gbar n a =
        (((2 * L n - |a|) / (2 * L n)) : ℝ) • G a)
    (hbudget :
      Gbound * (R / (2 * L n)) ≤ (1 : ℝ) / speed n) :
    dist (gbar n a) (G a) ≤ (1 : ℝ) / speed n := by
  rw [dist_eq_norm]

  set r : ℝ := (2 * L n - |a|) / (2 * L n)

  have hfactor : |r - 1| ≤ R / (2 * L n) := by
    simpa [r] using
      sharpCutoff_overlap_factor_error_le
        (L n) R a hL hR ha

  have hG : ‖G a‖ ≤ Gbound :=
    hG_bound a ha

  have hrewrite :
      r • G a - G a = (r - 1) • G a := by
    simpa using (sub_smul r (1 : ℝ) (G a)).symm

  calc
    ‖gbar n a - G a‖
        = ‖r • G a - G a‖ := by
            rw [hformula]
    _ = ‖(r - 1) • G a‖ := by
            rw [hrewrite]
    _ = ‖(r - 1 : ℝ)‖ * ‖G a‖ := by
            rw [norm_smul]
    _ = |r - 1| * ‖G a‖ := by
            rw [Real.norm_eq_abs]
    _ = ‖G a‖ * |r - 1| := by
            ring
    _ ≤ Gbound * (R / (2 * L n)) := by
            exact
              mul_le_mul
                hG
                hfactor
                (abs_nonneg _)
                hGbound_nonneg
    _ ≤ (1 : ℝ) / speed n :=
            hbudget

end

end RHFormalization
