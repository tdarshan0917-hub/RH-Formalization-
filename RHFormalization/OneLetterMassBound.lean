import RHFormalization.OneLetterTPairedMass
import RHFormalization.ShortTimeUIntegral

/-!
# RHFormalization.OneLetterMassBound
**Item 4a part 3 (GPT step 2 complete): the u-integrated exact Duhamel
remainder mass bound.**
`∫₀ᵗ |Tr(D(t−u)·oneWord(u)·T_a)| du ≤ √t·(SupV·√2/√π)` — the a.e.-
domination endgame with majorant `(C₁/(2√π))·(t−u)^{−1/2}`, evaluated by
`integral_sub_rpow_neg_half`. No u-prefactor: strictly better than the
quad channel's t^{3/2}.
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

/-- The one-letter T-paired trace function. -/
noncomputable def oneTraceTFn (qs : Finset ℕ) (a t u : ℝ) : ℝ :=
  |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
      * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace|

theorem continuous_oneTraceTFn (qs : Finset ℕ) (a t : ℝ) :
    Continuous (fun u => oneTraceTFn (N := N) qs a t u) := by
  unfold oneTraceTFn
  have hmul : Continuous (fun u : ℝ =>
      (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)) := by
    unfold oneWordMatrix
    fun_prop
  have htr : Continuous (fun u : ℝ =>
      ((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace) := by
    first
      | exact hmul.matrix_trace
      | exact Continuous.matrix_trace hmul
      | (apply Continuous.matrix_trace; exact hmul)
  exact htr.abs

/-- **The one-letter mass bound**: `∫₀ᵗ oneTraceTFn ≤ √t·(SupV·√2/√π)`. -/
theorem oneLetter_mass_le (qs : Finset ℕ) (hN : 0 < N)
    (a t : ℝ) (ht : 0 < t) :
    (∫ u in (0:ℝ)..t, oneTraceTFn (N := N) qs a t u)
      ≤ Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi := by
  set C : ℝ := SupVConst * Real.sqrt 2 with hC
  have hSnn : 0 ≤ SupVConst := SupVConst_nonneg_adm
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hfInt : IntervalIntegrable
      (fun u => oneTraceTFn (N := N) qs a t u) MeasureTheory.volume 0 t :=
    (continuous_oneTraceTFn qs a t).intervalIntegrable 0 t
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
      (fun u : ℝ => (C / (2 * Real.sqrt Real.pi)) * (t - u) ^ (-(1/2) : ℝ))
      MeasureTheory.volume 0 t := by
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
      oneTraceTFn (N := N) qs a t u
        ≤ (C / (2 * Real.sqrt Real.pi)) * (t - u) ^ (-(1/2) : ℝ) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hne] with u hune humem
    have hut : u < t := by
      refine lt_of_le_of_ne humem.2 ?_
      intro h
      exact hune (by simp [h])
    have htu : 0 < t - u := by linarith
    have hstep := oneWord_T_trace_sqrt_le qs hN t u humem.1 hut a
    have hmassage : (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
        = (1 / (2 * Real.sqrt Real.pi)) * (t - u) ^ (-(1/2) : ℝ) := by
      rw [sqrt_pi_div_arg (t - u) htu]
      rw [show (t - u) ^ (-(1/2) : ℝ) = 1 / Real.sqrt (t - u) from by
        rw [Real.rpow_neg (le_of_lt htu), Real.sqrt_eq_rpow, one_div]]
      have hπ : (0:ℝ) < Real.sqrt Real.pi :=
        Real.sqrt_pos.mpr Real.pi_pos
      have htu' : (0:ℝ) < Real.sqrt (t - u) := Real.sqrt_pos.mpr htu
      field_simp
    unfold oneTraceTFn at *
    calc |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (oneWordMatrix (N := N) qs u * galerkinT (N := N) 1 a)).trace|
        ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2) * C := hstep
      _ = (C / (2 * Real.sqrt Real.pi)) * (t - u) ^ (-(1/2) : ℝ) := by
          rw [hmassage]
          ring
  have hae : (fun u => oneTraceTFn (N := N) qs a t u)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0:ℝ) t)]
        (fun u : ℝ => (C / (2 * Real.sqrt Real.pi))
          * (t - u) ^ (-(1/2) : ℝ)) := hae'
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (le_of_lt ht) hfInt hgInt hae
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const_mul, integral_sub_rpow_neg_half t]
  rw [le_div_iff (Real.sqrt_pos.mpr Real.pi_pos)]
  have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp
  exact le_of_eq (by ring)

#print axioms oneTraceTFn
#print axioms oneLetter_mass_le

end

end RHFormalization
