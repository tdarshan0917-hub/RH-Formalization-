import RHFormalization.QuadRemainderTransformShortTime

/-!
# RHFormalization.QuadMassFnContinuity
**hcont discharge**: `quadRemainderMassFn` is continuous, so the
short-time transform bound holds unconditionally. Route: joint
(t,u)-continuity of `quadTraceFn` (same fun_prop skeleton as the banked
`continuous_quadTraceFn`), then the pin-proven parametric-integral lemma.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Joint (t,u)-continuity of the quadratic-remainder trace. -/
theorem continuous_quadTraceFn_joint (qs : Finset ℕ) :
    Continuous (fun p : ℝ × ℝ => quadTraceFn (N := N) qs p.1 p.2) := by
  unfold quadTraceFn
  have hF : Continuous (fun p : ℝ × ℝ =>
      NormedSpace.exp ((p.1 - p.2) • -galerkinK (N := N) 1)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * NormedSpace.exp (p.2 • -(galerkinK (N := N) 1
            + galerkinV (N := N) 1 qs ppWeightReal 1))) := by
    fun_prop
  have hinner : Continuous (fun u : ℝ =>
      ∫ s in (0 : ℝ)..u,
        NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * NormedSpace.exp (s • -(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1))) := by
    first
      | exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          hF continuous_id
      | exact continuous_parametric_intervalIntegral_of_continuous hF continuous_id
  have houter : Continuous (fun p : ℝ × ℝ =>
      (Matrix.diagonal fun m => heatWeight (N := N) 1 (p.1 - p.2) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1))) := by
    first
      | fun_prop
      | (unfold heatWeight; fun_prop)
  have hmul : Continuous (fun p : ℝ × ℝ =>
      ((Matrix.diagonal fun m => heatWeight (N := N) 1 (p.1 - p.2) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1)))
      * (∫ s in (0 : ℝ)..p.2,
          NormedSpace.exp ((p.2 - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1)))) :=
    houter.mul (hinner.comp continuous_snd)
  first
    | exact hmul.matrix_trace
    | exact Continuous.matrix_trace hmul
    | (apply Continuous.matrix_trace; exact hmul)

/-- **The hcont discharge**: the u-integrated mass is continuous in `t`. -/
theorem continuous_quadRemainderMassFn (qs : Finset ℕ) :
    Continuous (quadRemainderMassFn (N := N) qs) := by
  unfold quadRemainderMassFn
  first
    | exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (continuous_quadTraceFn_joint qs) continuous_id
    | exact continuous_parametric_intervalIntegral_of_continuous
        (continuous_quadTraceFn_joint qs) continuous_id

/-- **Unconditional short-time transform bound** — hcont discharged. -/
theorem quadRemainder_transform_shortTime_le' (qs : Finset ℕ) (hN : 0 < N)
    (t0 M : ℝ) (ht0 : 0 ≤ t0) (s : ℂ) (hM : |s.re| ≤ M) :
    ‖∫ t in (0:ℝ)..t0,
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ)‖
      ≤ Real.exp (M * t0)
          * ((2/5) * t0 ^ ((5:ℝ)/2) * (SupVConst ^ 2 / Real.sqrt Real.pi)) :=
  quadRemainder_transform_shortTime_le qs hN t0 M ht0 s hM
    (continuous_quadRemainderMassFn qs)

#print axioms continuous_quadTraceFn_joint
#print axioms continuous_quadRemainderMassFn
#print axioms quadRemainder_transform_shortTime_le'

end

end RHFormalization
