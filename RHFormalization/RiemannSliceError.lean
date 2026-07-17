import Mathlib

/-!
# Generic Riemann-slice error — G3-ii-b sub-brick 1
SENTINEL: slice-error-v2

ROUTE CARD
1. `slice_endpoint_riemann_error`: for C¹ f on [c,d],
   `|(d−c)·f(d) − ∫_c^d f| ≤ (d−c)·∫_c^d |f'|`.
   The one-slice engine of the cosine comparison: applied at
   c=(k−1)π/L, d=kπ/L, f=e^{−tξ²}cos(ξa), then summed over k.
2. Pure Mathlib real analysis; no repo objects.
-/

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory intervalIntegral

/-- **The slice estimate**: right-endpoint Riemann term vs the integral,
bounded by the slice's total variation. -/
theorem slice_endpoint_riemann_error (f f' : ℝ → ℝ) (c d : ℝ) (hcd : c ≤ d)
    (hderiv : ∀ x ∈ Set.uIcc c d, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (Set.uIcc c d)) :
    |(d - c) * f d - ∫ x in c..d, f x|
      ≤ (d - c) * ∫ x in c..d, |f' x| := by
  have hfc : ContinuousOn f (Set.uIcc c d) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume c d :=
    hfc.intervalIntegrable
  have hf'int : IntervalIntegrable f' volume c d :=
    hf'c.intervalIntegrable
  have habsint : IntervalIntegrable (fun x => |f' x|) volume c d :=
    hf'int.abs
  -- the constant M bounding every increment
  set M : ℝ := ∫ x in c..d, |f' x| with hM
  have hMnonneg : 0 ≤ M := by
    rw [hM]
    apply intervalIntegral.integral_nonneg hcd
    intro x _
    exact abs_nonneg _
  -- every increment |f d − f ξ| ≤ M for ξ ∈ [c,d]
  have hinc : ∀ ξ ∈ Set.Icc c d, |f d - f ξ| ≤ M := by
    intro ξ hξ
    have hξd : ξ ≤ d := hξ.2
    have hsub : Set.uIcc ξ d ⊆ Set.uIcc c d := by
      rw [Set.uIcc_of_le hξd, Set.uIcc_of_le hcd]
      exact Set.Icc_subset_Icc hξ.1 le_rfl
    have hftc : f d - f ξ = ∫ x in ξ..d, f' x := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hderiv x (hsub hx))
        ((hf'c.mono hsub).intervalIntegrable)
      linarith [h]
    rw [hftc]
    have h1 : |∫ x in ξ..d, f' x| ≤ ∫ x in ξ..d, |f' x| :=
      intervalIntegral.abs_integral_le_integral_abs hξd
    have h2 : (∫ x in ξ..d, |f' x|) ≤ M := by
      rw [hM]
      have hsplit : (∫ x in c..ξ, |f' x|) + (∫ x in ξ..d, |f' x|)
          = ∫ x in c..d, |f' x| := by
        apply intervalIntegral.integral_add_adjacent_intervals
        · exact (habsint.mono_set (by
            rw [Set.uIcc_of_le hξ.1, Set.uIcc_of_le hcd]
            exact Set.Icc_subset_Icc le_rfl hξd))
        · exact (habsint.mono_set (by
            rw [Set.uIcc_of_le hξd, Set.uIcc_of_le hcd]
            exact Set.Icc_subset_Icc hξ.1 le_rfl))
      have hfirst : 0 ≤ ∫ x in c..ξ, |f' x| := by
        apply intervalIntegral.integral_nonneg hξ.1
        intro x _
        exact abs_nonneg _
      linarith
    linarith
  -- (d−c)·f(d) − ∫f = ∫(f(d) − f(ξ))dξ
  have hconst : (d - c) * f d = ∫ _ξ in c..d, f d := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hdiff : (d - c) * f d - (∫ x in c..d, f x)
      = ∫ ξ in c..d, (f d - f ξ) := by
    rw [hconst, ← intervalIntegral.integral_sub
      (_root_.intervalIntegrable_const) hfint]
  rw [hdiff]
  calc |∫ ξ in c..d, (f d - f ξ)|
      ≤ ∫ ξ in c..d, |f d - f ξ| :=
        intervalIntegral.abs_integral_le_integral_abs hcd
    _ ≤ ∫ _ξ in c..d, M := by
        apply intervalIntegral.integral_mono_on hcd
        · exact (intervalIntegrable_const.sub hfint).abs |>.mono_set
            (by rw [Set.uIcc_of_le hcd])
        · exact _root_.intervalIntegrable_const
        · intro ξ hξ
          exact hinc ξ hξ
    _ = (d - c) * M := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

#print axioms slice_endpoint_riemann_error

end RHFormalization
