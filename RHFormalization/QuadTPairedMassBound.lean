import RHFormalization.QuadTPairedShortTimeMass
import RHFormalization.ShortTimeUIntegral
import RHFormalization.ShortTimeQuadMass

/-!
# RHFormalization.QuadTPairedMassBound
**Ledger item 3c part 3: the T-paired `t·√t` mass bound.**
`∫₀ᵗ quadTraceTFn ≤ t·√t·(SupV²·√2)/√π` — the banked
`shortTime_quadMass_le` endgame line-for-line with the T-paired pointwise
input (`quadTraceTFn_le`) and constant `SupVConst²·√2` fed to the generic
donors `sqrtConstant_le_rpow` / `integral_rpow_dominant`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory intervalIntegral

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

theorem continuous_quadTraceTFn (qs : Finset ℕ) (a t : ℝ) :
    Continuous (fun u => quadTraceTFn (N := N) qs a t u) := by
  unfold quadTraceTFn
  apply Continuous.abs
  apply Continuous.matrix_trace
  apply Continuous.mul
  · fun_prop
  · apply Continuous.mul _ continuous_const
    have hF : Continuous (fun p : ℝ × ℝ =>
        quadWordMatrix (N := N) qs p.1 p.2) := by
      unfold quadWordMatrix
      fun_prop
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hF continuous_id

/-- **The T-paired mass bound**: `∫₀ᵗ quadTraceTFn ≤ t·√t·(√2·SupV²)/√π`. -/
theorem quadTPaired_shortTime_mass_le (qs : Finset ℕ) (hN : 0 < N)
    (a t : ℝ) (ht : 0 < t) :
    (∫ u in (0:ℝ)..t, quadTraceTFn (N := N) qs a t u)
      ≤ t * Real.sqrt t * (SupVConst ^ 2 * Real.sqrt 2) / Real.sqrt Real.pi := by
  have hfInt : IntervalIntegrable
      (fun u => quadTraceTFn (N := N) qs a t u) MeasureTheory.volume 0 t :=
    (continuous_quadTraceTFn qs a t).intervalIntegrable 0 t
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
      (fun u : ℝ => (t * (SupVConst ^ 2 * Real.sqrt 2)
          / (2 * Real.sqrt Real.pi))
        * (t - u) ^ (-(1/2) : ℝ)) MeasureTheory.volume 0 t := by
    first
      | exact hrefl.const_mul _
      | exact IntervalIntegrable.const_mul _ hrefl
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
      quadTraceTFn (N := N) qs a t u
        ≤ (t * (SupVConst ^ 2 * Real.sqrt 2) / (2 * Real.sqrt Real.pi))
            * (t - u) ^ (-(1/2) : ℝ) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hne] with u hune humem
    have hut : u < t := by
      refine lt_of_le_of_ne humem.2 ?_
      intro h
      exact hune (by simp [h])
    calc quadTraceTFn (N := N) qs a t u
        ≤ u * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
            * (SupVConst ^ 2 * Real.sqrt 2)) :=
          quadTraceTFn_le qs hN a t u humem.1 hut
      _ ≤ (t * (SupVConst ^ 2 * Real.sqrt 2) / (2 * Real.sqrt Real.pi))
            * (t - u) ^ (-(1/2) : ℝ) :=
          sqrtConstant_le_rpow t u (SupVConst ^ 2 * Real.sqrt 2)
            humem.1 hut (by positivity)
  have hae : (fun u => quadTraceTFn (N := N) qs a t u)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0:ℝ) t)]
        (fun u : ℝ => (t * (SupVConst ^ 2 * Real.sqrt 2)
            / (2 * Real.sqrt Real.pi))
          * (t - u) ^ (-(1/2) : ℝ)) := hae'
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (le_of_lt ht) hfInt hgInt hae
  refine le_trans hmono ?_
  rw [integral_rpow_dominant t (SupVConst ^ 2 * Real.sqrt 2)]

#print axioms continuous_quadTraceTFn
#print axioms quadTPaired_shortTime_mass_le

end

end RHFormalization
