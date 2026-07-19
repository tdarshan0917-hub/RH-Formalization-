-- SENTINEL: spike-transfer-pillar-close-v2
import RHFormalization.SpikeTransferE2Bound
import RHFormalization.GalerkinFirstTermIsDuhamel1
import RHFormalization.GalerkinFullSandwichTraceSplit
import Mathlib

/-! # Core brick 6c-iv-c — PILLAR CLOSE: `|E₂(t)| ≤ C·t²`.
`E₂ = ∫ quadTraceFn` (bridge splits, first term cancels the order-1
integral), then the pointwise bound integrates to quadratic smallness:
the finite-stage D.SPIKE-TRANSFER M=2 remainder estimate, complete. -/

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

set_option maxHeartbeats 1600000

/-- Continuity of the bridge trace integrand. -/
theorem bridgeTrace_continuous (qs : Finset ℕ) (L t : ℝ) :
    Continuous (fun u : ℝ =>
      (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L)))).trace) := by
  first | fun_prop | continuity | (unfold heatWeight; fun_prop) | (unfold heatWeight; continuity)

/-- Continuity of the order-1 integrand in `u`. -/
theorem duhamel1_continuous (qs : Finset ℕ) (L t : ℝ) :
    Continuous (fun u : ℝ =>
      duhamel1Integrand (N := N) 1 qs ppWeightReal L t u) := by
  unfold duhamel1Integrand
  first | fun_prop | continuity | (unfold heatWeight; fun_prop) | (unfold heatWeight; continuity)

/-- **E₂ is exactly the quad-trace integral.** -/
theorem spikeTransferE2_eq_integral_quad (qs : Finset ℕ) (L t : ℝ) :
    spikeTransferE2 (N := N) 1 qs ppWeightReal L t
      = ∫ u in (0:ℝ)..t, quadTraceFn (N := N) qs L t u := by
  rw [spikeTransferE2_eq_bridge_add_order1]
  have hsplit : ∀ u : ℝ,
      (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L)))).trace
      = -(duhamel1Integrand (N := N) 1 qs ppWeightReal L t u)
        + quadTraceFn (N := N) qs L t u := by
    intro u
    rw [galerkinFullSandwich_trace_split (N := N) 1 qs ppWeightReal L t u,
      galerkinFirstSplitTerm_eq_neg_duhamel1 (N := N) 1 qs ppWeightReal L t u]
    rfl
  have hbridgeC := bridgeTrace_continuous (N := N) qs L t
  have hduhC := duhamel1_continuous (N := N) qs L t
  have hquadC : Continuous (fun u : ℝ => quadTraceFn (N := N) qs L t u) := by
    have heq : (fun u : ℝ => quadTraceFn (N := N) qs L t u)
        = fun u : ℝ =>
          ((Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
            * (-(galerkinV (N := N) 1 qs ppWeightReal L))
            * NormedSpace.exp (u • (-(galerkinK (N := N) L
                + galerkinV (N := N) 1 qs ppWeightReal L)))).trace)
          + duhamel1Integrand (N := N) 1 qs ppWeightReal L t u := by
      funext u
      rw [hsplit u]
      ring
    rw [heq]
    exact hbridgeC.add hduhC
  have hIduh : IntervalIntegrable
      (fun u : ℝ => duhamel1Integrand (N := N) 1 qs ppWeightReal L t u)
      MeasureTheory.volume 0 t := hduhC.intervalIntegrable 0 t
  have hIquad : IntervalIntegrable
      (fun u : ℝ => quadTraceFn (N := N) qs L t u)
      MeasureTheory.volume 0 t := hquadC.intervalIntegrable 0 t
  have hIneg : IntervalIntegrable
      (fun u : ℝ => -(duhamel1Integrand (N := N) 1 qs ppWeightReal L t u))
      MeasureTheory.volume 0 t := hIduh.neg
  have hcongr : (∫ u in (0:ℝ)..t,
      (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L)))).trace)
      = ∫ u in (0:ℝ)..t,
          (-(duhamel1Integrand (N := N) 1 qs ppWeightReal L t u)
            + quadTraceFn (N := N) qs L t u) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact hsplit u
  rw [hcongr, intervalIntegral.integral_add hIneg hIquad,
    intervalIntegral.integral_neg]
  ring

/-- **PILLAR CLOSE: the M=2 remainder is quadratically small.** -/
theorem spikeTransferE2_abs_le_t_sq (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : 0 ≤ t) :
    |spikeTransferE2 (N := N) 1 qs ppWeightReal L t|
      ≤ (Real.sqrt ((N:ℝ) * frobSq (galerkinV (N := N) 1 qs ppWeightReal L))
          * ((N:ℝ)^2
            * Real.sqrt (frobSq (galerkinV (N := N) 1 qs ppWeightReal L))))
        * t^2 := by
  set fV := frobSq (galerkinV (N := N) 1 qs ppWeightReal L) with hfV
  set C := Real.sqrt ((N:ℝ) * fV) * ((N:ℝ)^2 * Real.sqrt fV) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  rw [spikeTransferE2_eq_integral_quad]
  have hbd : ∀ u ∈ Set.uIoc (0:ℝ) t,
      ‖quadTraceFn (N := N) qs L t u‖ ≤ C * t := by
    intro u hu
    have huIoc : u ∈ Set.Ioc (0:ℝ) t := by rwa [Set.uIoc_of_le ht] at hu
    rw [Real.norm_eq_abs]
    refine le_trans (quadTraceFn_abs_le (N := N) qs L hL t u
      huIoc.1.le huIoc.2) ?_
    have hut := huIoc.2
    have hu0 := huIoc.1.le
    have hprod0 : (0:ℝ) ≤ (N:ℝ) * u * Real.sqrt fV :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hu0) (Real.sqrt_nonneg _)
    have hsq : Real.sqrt ((N:ℝ)^2 * ((N:ℝ) * u * Real.sqrt fV)^2)
        = (N:ℝ) * ((N:ℝ) * u * Real.sqrt fV) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg N),
        Real.sqrt_sq hprod0]
    rw [hsq, hC]
    have hs0 : (0:ℝ) ≤ Real.sqrt ((N:ℝ) * fV) := Real.sqrt_nonneg _
    have hs1 : (0:ℝ) ≤ Real.sqrt fV := Real.sqrt_nonneg _
    nlinarith [Nat.cast_nonneg (α := ℝ) N, mul_nonneg hs0 hs1]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs] at hnorm
  have habs : |t - 0| = t := by rw [sub_zero]; exact abs_of_nonneg ht
  rw [habs] at hnorm
  calc |∫ u in (0:ℝ)..t, quadTraceFn (N := N) qs L t u|
      ≤ C * t * t := hnorm
    _ = C * t^2 := by ring

#print axioms spikeTransferE2_eq_integral_quad
#print axioms spikeTransferE2_abs_le_t_sq

end

end RHFormalization
