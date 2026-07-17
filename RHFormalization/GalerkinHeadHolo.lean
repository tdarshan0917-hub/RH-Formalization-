import RHFormalization.GalerkinTailHolo
import RHFormalization.GalerkinHeadIntegralBound
import RHFormalization.BSideHeatKernelLaplaceEnvelope
import RHFormalization.BetaConvBound
import Mathlib

/-!
# GalerkinHeadHolo — the head `∫₀^{t₀}` is ENTIRE in `s`

ROUTE CARD
1. Target: `s ↦ ∫ t in Ioc 0 spikeT0, galQResIntegrand n s t` is differentiable at
   every `z₀ : ℂ`. Hence holomorphic on `Ω` a fortiori.
2. Objects: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (Mathlib),
   `shiftedHeatIntegrand_hasDerivAt` (banked), `shiftedHeatIntegrand_norm_le_bEnvelope`
   (banked), `intervalIntegrable_rpow_neg_half` (banked), `freeHeatDiagonal_eq_rpow` (banked).
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.KEY-FORM — the truncated transform is entire.
7. Consumer: with `galQRes_head_integral_bound` (banked), the head is a NORMAL FAMILY.

WHY THE HEAD IS ENTIRE AND `bRHS` IS NOT. `bRHS_differentiableAt` needs `Re s > 0`
because `bEnvelope c` is integrable on `Ioi 0` only for `c > 0`. On the BOUNDED
interval `Ioc 0 t₀`, `e^{-ct} ≤ e^{|c| t₀}` for every real `c`, so the constraint
vanishes. Clamping `M := max (…) 0` is what removes the half-plane — the same
mechanism as `exp_neg_re_le` in `GalerkinHeadIntegralBound`.

PIN NOTES. `rw` does not beta-reduce: insert `simp only []` before rewriting under
an unapplied lambda. `MeasureTheory.IntegrableOn.congr_fun` takes no dot notation.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory Set Filter
open scoped BigOperators

/-- The truncated `t^{-1/2}` dominator is integrable on `Ioc 0 t₀`. -/
theorem invSqrt_dominator_integrableOn (t0 A : ℝ) (ht0 : 0 < t0) :
    IntegrableOn (fun t : ℝ => A * (1 / Real.sqrt (4 * Real.pi * t))) (Set.Ioc 0 t0) := by
  have h1 := intervalIntegrable_rpow_neg_half t0
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le] at h1
  have h2 : IntegrableOn
      (fun t : ℝ => (A * (1 / (2 * Real.sqrt Real.pi))) * (t ^ (-(1:ℝ)/2)))
      (Set.Ioc 0 t0) := h1.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ioc
  intro t ht
  have htp : (0:ℝ) < t := ht.1
  have hfd := freeHeatDiagonal_eq_rpow t htp
  unfold freeHeatDiagonal at hfd
  simp only []
  rw [hfd]
  ring

/-- **No half-plane.** The B-atom is integrable on `Ioc 0 t₀` for every `z : ℂ`. -/
theorem shiftedHeatIntegrand_integrableOn_Ioc (a : ℝ) (z : ℂ) (t0 : ℝ) (ht0 : 0 < t0) :
    IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a z t) (Set.Ioc (0:ℝ) t0) := by
  set M : ℝ := max (-(z.re + 1/4)) 0 with hMdef
  have hM0 : (0:ℝ) ≤ M := le_max_right _ _
  have hMz : -(z.re + 1/4) ≤ M := le_max_left _ _
  have hdom := invSqrt_dominator_integrableOn t0 (Real.exp (M * t0)) ht0
  refine Integrable.mono' hdom (by
    unfold shiftedHeatIntegrand heatKernelG
    apply Measurable.aestronglyMeasurable
    fun_prop) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have htp : (0:ℝ) < t := ht.1
  have htT : t ≤ t0 := ht.2
  have hnorm := shiftedHeatIntegrand_norm_le_bEnvelope a z t htp
  unfold bEnvelope at hnorm
  refine le_trans hnorm ?_
  have hexp : Real.exp (-((z.re + 1/4) * t)) ≤ Real.exp (M * t0) := by
    apply Real.exp_le_exp.mpr
    calc -((z.re + 1/4) * t) = (-(z.re + 1/4)) * t := by ring
      _ ≤ M * t := mul_le_mul_of_nonneg_right hMz htp.le
      _ ≤ M * t0 := mul_le_mul_of_nonneg_left htT hM0
  have hpre : (0:ℝ) ≤ 1 / Real.sqrt (4 * Real.pi * t) := by positivity
  calc (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-((z.re + 1/4) * t))
      ≤ (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (M * t0) :=
        mul_le_mul_of_nonneg_left hexp hpre
    _ = Real.exp (M * t0) * (1 / Real.sqrt (4 * Real.pi * t)) := by ring

/-- The derivative dominator on `Ioc 0 t₀`, uniform over `{w | -(w.re+¼) ≤ M}`. -/
theorem deriv_dominated_Ioc (a : ℝ) (t0 M : ℝ) (ht0 : 0 < t0) (hM0 : 0 ≤ M)
    (z : ℂ) (hz : -(z.re + 1/4) ≤ M) (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) t0) :
    ‖-(t:ℂ) * shiftedHeatIntegrand a z t‖
      ≤ (t0 * Real.exp (M * t0)) * (1 / Real.sqrt (4 * Real.pi * t)) := by
  have htp : (0:ℝ) < t := ht.1
  have htT : t ≤ t0 := ht.2
  have hnorm := shiftedHeatIntegrand_norm_le_bEnvelope a z t htp
  have hstep : ‖-(t:ℂ) * shiftedHeatIntegrand a z t‖ = t * ‖shiftedHeatIntegrand a z t‖ := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
  rw [hstep]
  unfold bEnvelope at hnorm
  have hexp : Real.exp (-((z.re + 1/4) * t)) ≤ Real.exp (M * t0) := by
    apply Real.exp_le_exp.mpr
    calc -((z.re + 1/4) * t) = (-(z.re + 1/4)) * t := by ring
      _ ≤ M * t := mul_le_mul_of_nonneg_right hz htp.le
      _ ≤ M * t0 := mul_le_mul_of_nonneg_left htT hM0
  have hpre : (0:ℝ) ≤ 1 / Real.sqrt (4 * Real.pi * t) := by positivity
  calc t * ‖shiftedHeatIntegrand a z t‖
      ≤ t * ((1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-((z.re + 1/4) * t))) :=
        mul_le_mul_of_nonneg_left hnorm htp.le
    _ ≤ t0 * ((1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (M * t0)) := by
        apply mul_le_mul htT ?_ (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_left hexp hpre
    _ = (t0 * Real.exp (M * t0)) * (1 / Real.sqrt (4 * Real.pi * t)) := by ring

/-- **THE B-ATOM HEAD IS ENTIRE.** Differentiable at every `z₀ : ℂ`. -/
theorem bHeadAtom_differentiableAt (a : ℝ) (t0 : ℝ) (ht0 : 0 < t0) (z0 : ℂ) :
    DifferentiableAt ℂ
      (fun s : ℂ => ∫ t in Set.Ioc (0:ℝ) t0, shiftedHeatIntegrand a s t) z0 := by
  set U : Set ℂ := {w : ℂ | z0.re - 1 < w.re} with hUdef
  set M : ℝ := max (-z0.re + 3/4) 0 with hMdef
  have hM0 : (0:ℝ) ≤ M := le_max_right _ _
  have hMU : ∀ w ∈ U, -(w.re + 1/4) ≤ M := by
    intro w hw
    have hwre : z0.re - 1 < w.re := hw
    have h1 : -(w.re + 1/4) ≤ -z0.re + 3/4 := by linarith
    exact le_trans h1 (le_max_left _ _)
  have hUnhds : U ∈ nhds z0 := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
    simp only [Set.mem_setOf_eq]
    linarith
  have hmeas_one : ∀ (z : ℂ),
      AEStronglyMeasurable (fun t : ℝ => shiftedHeatIntegrand a z t)
        (volume.restrict (Set.Ioc (0:ℝ) t0)) := by
    intro z
    unfold shiftedHeatIntegrand heatKernelG
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmeas : ∀ᶠ (z : ℂ) in nhds z0,
      AEStronglyMeasurable (fun t : ℝ => shiftedHeatIntegrand a z t)
        (volume.restrict (Set.Ioc (0:ℝ) t0)) :=
    Filter.Eventually.of_forall hmeas_one
  have hint0 : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a z0 t)
      (Set.Ioc (0:ℝ) t0) volume :=
    shiftedHeatIntegrand_integrableOn_Ioc a z0 t0 ht0
  have hderiv_meas : AEStronglyMeasurable
      (fun t : ℝ => -(t:ℂ) * shiftedHeatIntegrand a z0 t)
      (volume.restrict (Set.Ioc (0:ℝ) t0)) := by
    apply AEStronglyMeasurable.mul ?_ (hmeas_one z0)
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioc (0:ℝ) t0)), ∀ z ∈ U,
      ‖-(t:ℂ) * shiftedHeatIntegrand a z t‖
        ≤ (t0 * Real.exp (M * t0)) * (1 / Real.sqrt (4 * Real.pi * t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    intro z hz
    exact deriv_dominated_Ioc a t0 M ht0 hM0 z (hMU z hz) t ht
  have hbound_int : IntegrableOn
      (fun t : ℝ => (t0 * Real.exp (M * t0)) * (1 / Real.sqrt (4 * Real.pi * t)))
      (Set.Ioc (0:ℝ) t0) volume :=
    invSqrt_dominator_integrableOn t0 (t0 * Real.exp (M * t0)) ht0
  have hderiv : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioc (0:ℝ) t0)), ∀ z ∈ U,
      HasDerivAt (fun w : ℂ => shiftedHeatIntegrand a w t)
        (-(t:ℂ) * shiftedHeatIntegrand a z t) z := by
    filter_upwards with t
    intro z _
    exact shiftedHeatIntegrand_hasDerivAt a t z
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun t : ℝ => (t0 * Real.exp (M * t0)) * (1 / Real.sqrt (4 * Real.pi * t)))
    (F := fun z t => shiftedHeatIntegrand a z t)
    (F' := fun z t => -(t:ℂ) * shiftedHeatIntegrand a z t)
    hUnhds hmeas hint0 hderiv_meas hbound hbound_int hderiv
  exact result.2.differentiableAt

/-- **THE F-ATOM HEAD IS ENTIRE.** Dominator is a CONSTANT: no `t^{-1/2}` here. -/
theorem fHeadAtom_differentiableAt (mu : ℝ) (t0 : ℝ) (ht0 : 0 < t0) (z0 : ℂ) :
    DifferentiableAt ℂ
      (fun s : ℂ => ∫ t in Set.Ioc (0:ℝ) t0, Complex.exp (-(s + (mu:ℂ)) * (t:ℂ))) z0 := by
  set U : Set ℂ := {w : ℂ | z0.re - 1 < w.re} with hUdef
  set M : ℝ := max (-(z0.re - 1) - mu) 0 with hMdef
  have hM0 : (0:ℝ) ≤ M := le_max_right _ _
  have hMU : ∀ w ∈ U, -(w.re + mu) ≤ M := by
    intro w hw
    have hwre : z0.re - 1 < w.re := hw
    have h1 : -(w.re + mu) ≤ -(z0.re - 1) - mu := by linarith
    exact le_trans h1 (le_max_left _ _)
  have hUnhds : U ∈ nhds z0 := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
    simp only [Set.mem_setOf_eq]; linarith
  have hcont : ∀ z : ℂ, Continuous (fun t : ℝ => Complex.exp (-(z + (mu:ℂ)) * (t:ℂ))) := by
    intro z; fun_prop
  have hmeas : ∀ᶠ (z : ℂ) in nhds z0, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(z + (mu:ℂ)) * (t:ℂ)))
      (volume.restrict (Set.Ioc (0:ℝ) t0)) :=
    Filter.Eventually.of_forall (fun z => (hcont z).aestronglyMeasurable)
  have hint0 : IntegrableOn (fun t : ℝ => Complex.exp (-(z0 + (mu:ℂ)) * (t:ℂ)))
      (Set.Ioc (0:ℝ) t0) volume := Continuous.integrableOn_Ioc (hcont z0)
  have hderiv_meas : AEStronglyMeasurable
      (fun t : ℝ => -(t:ℂ) * Complex.exp (-(z0 + (mu:ℂ)) * (t:ℂ)))
      (volume.restrict (Set.Ioc (0:ℝ) t0)) := by
    apply AEStronglyMeasurable.mul ?_ (hcont z0).aestronglyMeasurable
    apply Measurable.aestronglyMeasurable; fun_prop
  have hnormeq : ∀ (z : ℂ) (t : ℝ),
      ‖Complex.exp (-(z + (mu:ℂ)) * (t:ℂ))‖ = Real.exp (-(z.re + mu) * t) := by
    intro z t
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im]
  have hbound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioc (0:ℝ) t0)), ∀ z ∈ U,
      ‖-(t:ℂ) * Complex.exp (-(z + (mu:ℂ)) * (t:ℂ))‖ ≤ t0 * Real.exp (M * t0) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    intro z hz
    have htp : (0:ℝ) < t := ht.1
    have htT : t ≤ t0 := ht.2
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp, hnormeq]
    have hexp : Real.exp (-(z.re + mu) * t) ≤ Real.exp (M * t0) := by
      apply Real.exp_le_exp.mpr
      calc -(z.re + mu) * t ≤ M * t :=
            mul_le_mul_of_nonneg_right (hMU z hz) htp.le
        _ ≤ M * t0 := mul_le_mul_of_nonneg_left htT hM0
    calc t * Real.exp (-(z.re + mu) * t)
        ≤ t0 * Real.exp (-(z.re + mu) * t) :=
          mul_le_mul_of_nonneg_right htT (Real.exp_pos _).le
      _ ≤ t0 * Real.exp (M * t0) :=
          mul_le_mul_of_nonneg_left hexp (by linarith)
  have hbound_int : IntegrableOn (fun _ : ℝ => t0 * Real.exp (M * t0))
      (Set.Ioc (0:ℝ) t0) volume := Continuous.integrableOn_Ioc continuous_const
  have hderiv : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioc (0:ℝ) t0)), ∀ z ∈ U,
      HasDerivAt (fun w : ℂ => Complex.exp (-(w + (mu:ℂ)) * (t:ℂ)))
        (-(t:ℂ) * Complex.exp (-(z + (mu:ℂ)) * (t:ℂ))) z := by
    filter_upwards with t
    intro z _
    have h1 : HasDerivAt (fun w : ℂ => -(w + (mu:ℂ)) * (t:ℂ)) (-(t:ℂ)) z := by
      have := ((hasDerivAt_id z).add_const ((mu:ℝ) : ℂ)).neg.mul_const (t:ℂ)
      simpa using this
    have h2 := h1.cexp
    convert h2 using 1
    ring

  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : ℝ => t0 * Real.exp (M * t0))
    (F := fun z t => Complex.exp (-(z + (mu:ℂ)) * (t:ℂ)))
    (F' := fun z t => -(t:ℂ) * Complex.exp (-(z + (mu:ℂ)) * (t:ℂ)))
    hUnhds hmeas hint0 hderiv_meas hbound hbound_int hderiv
  exact result.2.differentiableAt

/-- The B-head, as a finite sum of atoms. -/
theorem galBHead_eq_sum (n : ℕ) (s : ℂ) (t0 : ℝ) (ht0 : 0 < t0) :
    (∫ t in Set.Ioc (0:ℝ) t0, galBIntegrand n s t)
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * ∫ t in Set.Ioc (0:ℝ) t0, shiftedHeatIntegrand q.center s t := by
  unfold galBIntegrand
  rw [integral_finsetSum _ (fun q _ =>
    (shiftedHeatIntegrand_integrableOn_Ioc q.center s t0 ht0).const_mul q.weightC)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact integral_const_mul _ _

/-- The F-head, as a finite sum of atoms. -/
theorem galFHead_eq_sum (n : ℕ) (s : ℂ) (t0 : ℝ) (ht0 : 0 < t0) :
    (∫ t in Set.Ioc (0:ℝ) t0, galFIntegrand n s t)
      = admDensityC n * ∑ i : Fin (admN n),
          ∫ t in Set.Ioc (0:ℝ) t0,
            Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (t:ℂ)) := by
  have hint : ∀ i : Fin (admN n), IntegrableOn
      (fun t : ℝ => Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (t:ℂ)))
      (Set.Ioc (0:ℝ) t0) volume := by
    intro i
    apply Continuous.integrableOn_Ioc
    fun_prop
  unfold galFIntegrand
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum _ (fun i _ => hint i)

/-- **THE B-HEAD IS ENTIRE.** -/
theorem galBHead_differentiableAt (n : ℕ) (t0 : ℝ) (ht0 : 0 < t0) (z0 : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ t in Set.Ioc (0:ℝ) t0, galBIntegrand n s t) z0 := by
  have hEq : (fun s : ℂ => ∫ t in Set.Ioc (0:ℝ) t0, galBIntegrand n s t)
      = fun s : ℂ => ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * ∫ t in Set.Ioc (0:ℝ) t0, shiftedHeatIntegrand q.center s t := by
    funext s; exact galBHead_eq_sum n s t0 ht0
  rw [hEq]
  apply DifferentiableAt.fun_sum
  intro q _
  exact (bHeadAtom_differentiableAt q.center t0 ht0 z0).const_mul q.weightC

/-- **THE F-HEAD IS ENTIRE.** -/
theorem galFHead_differentiableAt (n : ℕ) (t0 : ℝ) (ht0 : 0 < t0) (z0 : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ t in Set.Ioc (0:ℝ) t0, galFIntegrand n s t) z0 := by
  have hEq : (fun s : ℂ => ∫ t in Set.Ioc (0:ℝ) t0, galFIntegrand n s t)
      = fun s : ℂ => admDensityC n * ∑ i : Fin (admN n),
          ∫ t in Set.Ioc (0:ℝ) t0,
            Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (t:ℂ)) := by
    funext s; exact galFHead_eq_sum n s t0 ht0
  rw [hEq]
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro i _
  exact fHeadAtom_differentiableAt (admMu n i) t0 ht0 z0

/-- **THE HEAD IS ENTIRE.** Differentiable at every `z₀ : ℂ`. -/
theorem galQResHead_differentiableAt (n : ℕ) (z0 : ℂ) :
    DifferentiableAt ℂ (galHead n) z0 := by
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  have hFint : ∀ s : ℂ, IntegrableOn (fun t : ℝ => galFIntegrand n s t)
      (Set.Ioc (0:ℝ) spikeT0) volume := by
    intro s
    apply Continuous.integrableOn_Ioc
    unfold galFIntegrand
    fun_prop
  have hBint : ∀ s : ℂ, IntegrableOn (fun t : ℝ => galBIntegrand n s t)
      (Set.Ioc (0:ℝ) spikeT0) volume := by
    intro s
    unfold galBIntegrand
    refine MeasureTheory.integrable_finset_sum
      (activePrimePowerPairsCenterBelow (admR n)) (fun q _ => ?_)
    exact (shiftedHeatIntegrand_integrableOn_Ioc q.center s spikeT0 hT).const_mul q.weightC
  have hEq : galHead n
      = fun s : ℂ => (∫ t in Set.Ioc (0:ℝ) spikeT0, galFIntegrand n s t)
          - (∫ t in Set.Ioc (0:ℝ) spikeT0, galBIntegrand n s t) := by
    funext s
    unfold galHead galQResIntegrand
    exact MeasureTheory.integral_sub (hFint s) (hBint s)
  rw [hEq]
  exact (galFHead_differentiableAt n spikeT0 hT z0).sub
    (galBHead_differentiableAt n spikeT0 hT z0)

#print axioms invSqrt_dominator_integrableOn
#print axioms shiftedHeatIntegrand_integrableOn_Ioc
#print axioms deriv_dominated_Ioc
#print axioms bHeadAtom_differentiableAt
#print axioms fHeadAtom_differentiableAt
#print axioms galBHead_eq_sum
#print axioms galFHead_eq_sum
#print axioms galBHead_differentiableAt
#print axioms galFHead_differentiableAt
#print axioms galQResHead_differentiableAt

end RHFormalization
