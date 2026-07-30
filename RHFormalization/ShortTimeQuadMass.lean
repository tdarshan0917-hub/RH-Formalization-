-- SENTINEL: short-time-quad-mass-v2
import RHFormalization.QuadRemainderSqrtIntegrated
import RHFormalization.ShortTimeUIntegral
import Mathlib

/-!
# Brick (c): the assembled short-time quadratic mass

`∫₀ᵗ |tr(D(t−u)·(−V)·Inner(u))| du ≤ t·√t·SupVConst²/√π`

Chain: sqrt-variant simplex bound (banked) → pointwise domination by the
rpow integrand (banked), a.e. on [0,t] (the endpoint u=t is null) →
`integral_mono_ae_restrict` → integrated dominant (banked). Continuity of
the LHS via the parametric interval-integral lemma with variable endpoint.
N-free, qs-uniform, α-uniform; `t^{3/2}` is t-integrable on (0,t₀]:
the short-time quadratic sector mass is CLOSED.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The quadratic-remainder trace as a function of the outer Duhamel time. -/
noncomputable def quadTraceFn (qs : Finset ℕ) (t : ℝ) (u : ℝ) : ℝ :=
  ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
      * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
      * ∫ s in (0 : ℝ)..u,
          NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1))).trace

/-- Continuity in `u` of the quadratic-remainder trace. -/
theorem continuous_quadTraceFn (qs : Finset ℕ) (t : ℝ) :
    Continuous (quadTraceFn (N := N) qs t) := by
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
      | exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (a₀ := (0:ℝ)) hF continuous_id
  have houter : Continuous (fun u : ℝ =>
      (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1))) := by
    first
      | fun_prop
      | (apply Continuous.mul _ continuous_const
         apply Continuous.matrix_diagonal
         intro m
         unfold heatWeight
         fun_prop)
      | (unfold heatWeight; fun_prop)
  have hmul : Continuous (fun u : ℝ =>
      ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1)))
      * (∫ s in (0 : ℝ)..u,
          NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
            * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
            * NormedSpace.exp (s • -(galerkinK (N := N) 1
                + galerkinV (N := N) 1 qs ppWeightReal 1)))) :=
    houter.mul hinner
  first
    | exact hmul.matrix_trace
    | exact Continuous.matrix_trace hmul
    | (apply Continuous.matrix_trace
       exact hmul)

/-- **THE SHORT-TIME QUADRATIC MASS.** N-free, qs-uniform, α-uniform. -/
theorem shortTime_quadMass_le (qs : Finset ℕ) (hN : 0 < N)
    (t : ℝ) (ht : 0 < t) :
    ∫ u in (0:ℝ)..t, |quadTraceFn (N := N) qs t u|
      ≤ t * Real.sqrt t * SupVConst ^ 2 / Real.sqrt Real.pi := by
  -- integrability of the LHS
  have hfInt : IntervalIntegrable
      (fun u => |quadTraceFn (N := N) qs t u|) MeasureTheory.volume 0 t :=
    ((continuous_quadTraceFn qs t).abs).intervalIntegrable 0 t
  -- integrability of the rpow dominant
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1/2) : ℝ))
      MeasureTheory.volume 0 t := by
    first
      | exact intervalIntegral.intervalIntegrable_rpow'
          (by norm_num : (-1:ℝ) < -(1/2))
      | exact intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1/2))
  have hrefl : IntervalIntegrable (fun u : ℝ => (t - u) ^ (-(1/2) : ℝ))
      MeasureTheory.volume 0 t := by
    have h := hbase.comp_sub_left t
    have hend1 : t - t = (0:ℝ) := by ring
    have hend2 : t - 0 = t := by ring
    rw [hend1, hend2] at h
    exact h.symm
  have hgInt : IntervalIntegrable
      (fun u : ℝ => (t * SupVConst ^ 2 / (2 * Real.sqrt Real.pi))
        * (t - u) ^ (-(1/2) : ℝ)) MeasureTheory.volume 0 t := by
    first
      | exact hrefl.const_mul _
      | exact IntervalIntegrable.const_mul _ hrefl
  -- the a.e. domination on Icc 0 t (endpoint u = t is null)
  have h0 : MeasureTheory.volume ({t} : Set ℝ) = 0 := by
    first
      | exact measure_singleton t
      | exact Real.volume_singleton
      | simp
  have hne : ∀ᵐ u : ℝ ∂MeasureTheory.volume, u ∉ ({t} : Set ℝ) := by
    first
      | exact MeasureTheory.measure_zero_iff_ae_nmem.mp h0
      | exact MeasureTheory.measure_zero_iff_ae_notMem.mp h0
      | exact MeasureTheory.ae_iff.mpr (by simpa using h0)
  have hae' : ∀ᵐ u : ℝ ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) t)),
      |quadTraceFn (N := N) qs t u|
        ≤ (t * SupVConst ^ 2 / (2 * Real.sqrt Real.pi))
            * (t - u) ^ (-(1/2) : ℝ) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hne] with u hune humem
    have hut : u < t := by
      refine lt_of_le_of_ne humem.2 ?_
      intro h
      exact hune (by simp [h])
    calc |quadTraceFn (N := N) qs t u|
        ≤ u * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
            * SupVConst ^ 2) :=
          quadRemainder_trace_sqrt_le qs hN t u humem.1 hut
      _ ≤ (t * SupVConst ^ 2 / (2 * Real.sqrt Real.pi))
            * (t - u) ^ (-(1/2) : ℝ) :=
          sqrtConstant_le_rpow t u (SupVConst ^ 2) humem.1 hut (sq_nonneg _)
  have hae : (fun u => |quadTraceFn (N := N) qs t u|)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0:ℝ) t)]
        (fun u : ℝ => (t * SupVConst ^ 2 / (2 * Real.sqrt Real.pi))
          * (t - u) ^ (-(1/2) : ℝ)) := hae'
  -- monotone integration against the dominant, then evaluate
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (le_of_lt ht) hfInt hgInt hae
  refine le_trans hmono ?_
  rw [integral_rpow_dominant t (SupVConst ^ 2)]

#print axioms continuous_quadTraceFn
#print axioms shortTime_quadMass_le

end

end RHFormalization
