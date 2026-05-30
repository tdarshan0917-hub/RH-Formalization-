import RHFormalization.CanonicalPrimePowerDWindowSpeedAPI

/-!
# RHFormalization.DCanonicalWindowSharpCutoffScalar

Scalar sharp-cutoff estimate behind D.CANONICAL-WINDOW.

This file formalizes the algebraic heart of the proof:

  gbar_{t,L}(a) = G_t(a) * (2L - |a|) / (2L)

on the region |a| ≤ L, and therefore on |a| ≤ R ≤ L,

  |gbar_{t,L}(a) - G_t(a)|
    ≤ sup_{|a|≤R} |G_t(a)| * R / (2L).

This is the scalar estimate needed to build
`DCanonicalWindowCompactSpeedAPI.h_compact_window_speed_rate`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The normalized sharp-cutoff overlap factor differs from `1` by at most
`R / (2L)` on `|a| ≤ R`.

This is the algebraic core of

  (2L - |a|)/(2L) → 1

uniformly on bounded `a`-intervals.
-/
theorem sharpCutoff_overlap_factor_error_le
    (L R a : ℝ)
    (hL : 0 < L)
    (_hR : 0 ≤ R)
    (ha : |a| ≤ R) :
    |((2 * L - |a|) / (2 * L)) - 1| ≤ R / (2 * L) := by
  have hden_pos : 0 < 2 * L := by
    nlinarith
  have hden_ne : 2 * L ≠ 0 := ne_of_gt hden_pos
  have hcalc :
      ((2 * L - |a|) / (2 * L)) - 1 =
        -(|a| / (2 * L)) := by
    field_simp [hden_ne]
    ring
  calc
    |((2 * L - |a|) / (2 * L)) - 1|
        = |- (|a| / (2 * L))| := by
            rw [hcalc]
    _ = |a| / (2 * L) := by
            rw [abs_neg]
            exact abs_of_nonneg
              (div_nonneg (abs_nonneg a) (le_of_lt hden_pos))
    _ ≤ R / (2 * L) := by
            exact div_le_div_of_nonneg_right ha (le_of_lt hden_pos)

/--
If `G` is bounded by `Gbound` on `|a| ≤ R`, then the normalized sharp-cutoff
kernel error is bounded by `Gbound * R / (2L)` on that interval.
-/
theorem sharpCutoff_normalized_kernel_error_le
    (G : ℝ → ℝ)
    (Gbound L R a : ℝ)
    (hL : 0 < L)
    (hR : 0 ≤ R)
    (hGbound_nonneg : 0 ≤ Gbound)
    (ha : |a| ≤ R)
    (hG_bound : ∀ x : ℝ, |x| ≤ R → |G x| ≤ Gbound) :
    |G a * ((2 * L - |a|) / (2 * L)) - G a|
      ≤ Gbound * (R / (2 * L)) := by
  have hfactor :
      |((2 * L - |a|) / (2 * L)) - 1| ≤ R / (2 * L) :=
    sharpCutoff_overlap_factor_error_le L R a hL hR ha
  have hGa : |G a| ≤ Gbound := hG_bound a ha
  have hrewrite :
      G a * ((2 * L - |a|) / (2 * L)) - G a =
        G a * (((2 * L - |a|) / (2 * L)) - 1) := by
    ring
  calc
    |G a * ((2 * L - |a|) / (2 * L)) - G a|
        = |G a * (((2 * L - |a|) / (2 * L)) - 1)| := by
            rw [hrewrite]
    _ = |G a| * |((2 * L - |a|) / (2 * L)) - 1| := by
            rw [abs_mul]
    _ ≤ Gbound * (R / (2 * L)) := by
            exact
              mul_le_mul
                hGa
                hfactor
                (abs_nonneg _)
                hGbound_nonneg

end

end RHFormalization
