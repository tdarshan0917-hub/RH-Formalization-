import RHFormalization.ShortTimeQuadMass
import RHFormalization.ShortTimeTransformBound

/-!
# RHFormalization.QuadRemainderTransformShortTime
**First transform-regime brick toward hSC.** The short-time Laplace
transform of the u-integrated quadratic Duhamel remainder is bounded,
uniformly over `|Re s| ≤ M`: composes `shortTime_quadMass_le`
(t^{3/2} mass, N-free, qs-uniform) into `shortTime_transform_le` (T1a).
DOWNSTREAM: long-time partner rides `quadRemainder_trace_diag_le`;
together → transform of spike remainder bounded on Ω-compacts →
`adaptivePairedTheta_split` → `decodedBulkSeam_eq_core_form` → hSC.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral

variable {N : ℕ}

/-- The u-integrated quadratic remainder mass at time `t`. -/
noncomputable def quadRemainderMassFn (qs : Finset ℕ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, quadTraceFn (N := N) qs t u

/-- Pointwise `t^{3/2}` bound for the mass function on `(0, t0]`,
directly from the banked short-time quadratic mass. -/
theorem quadRemainderMassFn_abs_le (qs : Finset ℕ) (hN : 0 < N)
    (t : ℝ) (ht : 0 < t) :
    |quadRemainderMassFn (N := N) qs t|
      ≤ t ^ ((3:ℝ)/2) * (SupVConst ^ 2 / Real.sqrt Real.pi) := by
  unfold quadRemainderMassFn
  have habs : |∫ u in (0:ℝ)..t, quadTraceFn (N := N) qs t u|
      ≤ ∫ u in (0:ℝ)..t, |quadTraceFn (N := N) qs t u| := by
    first
      | exact intervalIntegral.abs_integral_le_integral_abs ht.le
      | exact intervalIntegral.abs_integral_le ht.le
      | (apply intervalIntegral.norm_integral_le_integral_norm ht.le)
  refine habs.trans ((shortTime_quadMass_le qs hN t ht).trans (le_of_eq ?_))
  have hts : t ^ ((3:ℝ)/2) = t * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    rw [show ((3:ℝ)/2) = 1 + (1/2 : ℝ) by norm_num]
    rw [Real.rpow_add ht, Real.rpow_one]
  rw [hts]
  ring

/-- **Short-time transform bound for the quadratic remainder.**
Uniform over `|Re s| ≤ M`; N-free, qs-uniform constants. -/
theorem quadRemainder_transform_shortTime_le (qs : Finset ℕ) (hN : 0 < N)
    (t0 M : ℝ) (ht0 : 0 ≤ t0) (s : ℂ) (hM : |s.re| ≤ M)
    (hcont : Continuous (quadRemainderMassFn (N := N) qs)) :
    ‖∫ t in (0:ℝ)..t0,
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ)‖
      ≤ Real.exp (M * t0)
          * ((2/5) * t0 ^ ((5:ℝ)/2) * (SupVConst ^ 2 / Real.sqrt Real.pi)) := by
  refine shortTime_transform_le (quadRemainderMassFn (N := N) qs) hcont
    t0 (SupVConst ^ 2 / Real.sqrt Real.pi) M ht0 ?_ ?_ s hM
  · positivity
  · intro t htmem
    rcases eq_or_lt_of_le htmem.1 with h0 | hpos
    · rw [← h0]
      unfold quadRemainderMassFn
      rw [intervalIntegral.integral_same]
      simp
    · exact (quadRemainderMassFn_abs_le qs hN t hpos).trans
        (le_of_eq (by ring))

#print axioms quadRemainderMassFn
#print axioms quadRemainderMassFn_abs_le
#print axioms quadRemainder_transform_shortTime_le

end

end RHFormalization
