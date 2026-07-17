import RHFormalization.GalerkinHeadBound
import RHFormalization.BetaConvBound
import RHFormalization.DTailFreeHeatTraceBound
import Mathlib

/-!
# GalerkinHeadIntegralBound — the head integral, bounded at ANY parabola depth

ROUTE CARD
1. Target: `‖∫ t in Ioc 0 spikeT0, galQResIntegrand n s t‖ ≤ C(K)`, uniform in `n`,
   uniform on any compact `K ⊆ ℂ`. NO half-plane hypothesis on `s`.
2. Objects: `galQRes_integrand_short_time_bound` (banked pointwise dominator),
   `freeHeatDiagonal_eq_rpow` (banked, DTailFreeHeatTraceBound),
   `intervalIntegrable_rpow_neg_half` (BetaConvBound), `Integrable.mono'`,
   `norm_integral_le_of_norm_le`, `IsCompact.exists_isMaxOn`.
3. Raw B on Ω? NO. 4. R = F − raw B? NO — genuine `R_stage`. 5. True outright.
6. Manuscript: D.KEY-FORM. The truncated transform `∫₀^{t₀}` is entire in `s`;
   `|e^{-st}| ≤ e^{M_K t₀}` on `(0,t₀]` needs no right half-plane.
7. Consumer: the `t₀`-split; thence `DBFFO3ParabolaDepthHstar`.

WHY DEPTH IS FREE. The pointwise bound is `e^{-Re(s)·t}·((4πt)^{-1/2} + C)`.
On a compact `K`, set `M := max (sup_K (-Re s)) 0 ≥ 0`; then on `(0,t₀]`,
`-Re(s)·t ≤ M·t ≤ M·t₀`, so the exponential is `≤ e^{M·t₀}`. The only
`t`-singularity is `t^{-1/2}`, integrable at `0`. Nothing anywhere requires
`Re(s) > 0`, or `Re √(s+¼) > ½ + δ`.

The `max … 0` is load-bearing: for `K` strictly inside the right half-plane,
`sup_K (-Re s) < 0`, and `-Re(s)·t ≤ (sup)·t₀` is FALSE. Clamping at `0` fixes it.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory
open scoped BigOperators

/-- The dominator `A·t^{-1/2} + B` is integrable on `Ioc 0 t₀`. -/
theorem dominator_integrableOn (t0 : ℝ) (ht0 : 0 ≤ t0) (A B : ℝ) :
    IntegrableOn (fun t : ℝ => A * (t ^ (-(1:ℝ)/2)) + B) (Set.Ioc 0 t0) := by
  have h1 := intervalIntegrable_rpow_neg_half t0
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0] at h1
  have h2 : IntervalIntegrable (fun _ : ℝ => B) volume 0 t0 := intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0] at h2
  exact (h1.const_mul A).add h2

/-- `heatKernelG` is continuous on `Ioc 0 t₀` (the `(4πt)^{-1/2}` pole sits at `t = 0`). -/
theorem heatKernelG_continuousOn_Ioc (a t0 : ℝ) :
    ContinuousOn (fun t : ℝ => heatKernelG t a) (Set.Ioc 0 t0) := by
  have hb : (fun t : ℝ => heatKernelG t a)
      = fun t : ℝ => Complex.ofReal (heatKernelRealScalar t a) := by
    funext t; exact heatKernelG_eq_realScalar t a
  rw [hb]
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  unfold heatKernelRealScalar
  have hsqrt : ContinuousOn (fun t : ℝ => Real.sqrt (4 * Real.pi * t)) (Set.Ioc 0 t0) :=
    Real.continuous_sqrt.comp_continuousOn (by fun_prop)
  have hne : ∀ t ∈ Set.Ioc (0:ℝ) t0, Real.sqrt (4 * Real.pi * t) ≠ 0 := by
    intro t ht
    have h1 : (0:ℝ) < t := ht.1
    have h2 : (0:ℝ) < 4 * Real.pi * t := by positivity
    exact Real.sqrt_ne_zero'.mpr h2
  have hne4 : ∀ t ∈ Set.Ioc (0:ℝ) t0, (4:ℝ) * t ≠ 0 := by
    intro t ht
    have h1 : (0:ℝ) < t := ht.1
    positivity
  exact (continuousOn_const.div hsqrt hne).mul
    (ContinuousOn.rexp (continuousOn_const.div (by fun_prop) hne4))

/-- The genuine residual integrand is continuous on `Ioc 0 t₀`, for every `s : ℂ`. -/
theorem galQRes_continuousOn_Ioc (n : ℕ) (s : ℂ) (t0 : ℝ) :
    ContinuousOn (fun t : ℝ => galQResIntegrand n s t) (Set.Ioc 0 t0) := by
  unfold galQResIntegrand
  refine ContinuousOn.sub ?_ ?_
  · have hc : Continuous (fun t : ℝ => galFIntegrand n s t) := by
      unfold galFIntegrand; fun_prop
    exact hc.continuousOn
  · unfold galBIntegrand
    refine continuousOn_finsetSum _ (fun q _ => ?_)
    unfold shiftedHeatIntegrand
    exact continuousOn_const.mul
      ((((Complex.continuous_exp.comp (by fun_prop)).continuousOn).mul
        ((Complex.continuous_exp.comp (by fun_prop)).continuousOn)).mul
          (heatKernelG_continuousOn_Ioc q.center t0))

/-- The exponential damping factor, clamped. `M ≥ 0` is load-bearing. -/
theorem exp_neg_re_le (M t t0 r : ℝ) (hM0 : 0 ≤ M) (hr : -r ≤ M)
    (ht : 0 < t) (htT : t ≤ t0) :
    Real.exp (-r * t) ≤ Real.exp (M * t0) := by
  apply Real.exp_le_exp.mpr
  calc -r * t ≤ M * t := mul_le_mul_of_nonneg_right hr ht.le
    _ ≤ M * t0 := mul_le_mul_of_nonneg_left htT hM0

/-- A nonnegative uniform bound for `-Re s` on a compact set. -/
theorem exists_nonneg_neg_re_bound (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ K, -s.re ≤ M := by
  obtain ⟨s0, hs0, hmax⟩ := hK.exists_isMaxOn hne
    (Complex.continuous_re.neg.continuousOn)
  refine ⟨max (-s0.re) 0, le_max_right _ _, fun s hs => ?_⟩
  exact le_trans (hmax hs) (le_max_left _ _)

/-- **INTEGRABILITY ON THE HEAD, FOR EVERY `s : ℂ`.** No half-plane. -/
theorem galQRes_integrableOn_head (n : ℕ) (s : ℂ) :
    IntegrableOn (fun t : ℝ => galQResIntegrand n s t) (Set.Ioc 0 spikeT0) := by
  obtain ⟨C, hC0, hbd⟩ := galQRes_integrand_short_time_bound
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  set M : ℝ := max (-s.re) 0 with hMdef
  have hM0 : (0:ℝ) ≤ M := le_max_right _ _
  have hMs : -s.re ≤ M := le_max_left _ _
  set E : ℝ := Real.exp (M * spikeT0) with hE
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  have hdom : IntegrableOn
      (fun t : ℝ => (E * (1 / (2 * Real.sqrt Real.pi))) * (t ^ (-(1:ℝ)/2)) + E * C)
      (Set.Ioc 0 spikeT0) := dominator_integrableOn spikeT0 hT.le _ _
  refine Integrable.mono' hdom
    ((galQRes_continuousOn_Ioc n s spikeT0).aestronglyMeasurable measurableSet_Ioc) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have ht0 : (0:ℝ) < t := ht.1
  have htT : t ≤ spikeT0 := ht.2
  have hb := hbd n s t ht0 htT
  have hexp : Real.exp (-s.re * t) ≤ E := exp_neg_re_le M t spikeT0 s.re hM0 hMs ht0 htT
  have hfd : freeHeatDiagonal t = 1 / (2 * Real.sqrt Real.pi) * (t ^ (-(1:ℝ)/2)) :=
    freeHeatDiagonal_eq_rpow t ht0
  have hfd0 : (0:ℝ) ≤ freeHeatDiagonal t := freeHeatDiagonal_nonneg t
  calc ‖galQResIntegrand n s t‖
      ≤ Real.exp (-s.re * t) * (freeHeatDiagonal t + C) := hb
    _ ≤ E * (freeHeatDiagonal t + C) :=
        mul_le_mul_of_nonneg_right hexp (by linarith)
    _ = (E * (1 / (2 * Real.sqrt Real.pi))) * (t ^ (-(1:ℝ)/2)) + E * C := by
        rw [hfd]; ring

/-- **THE HEAD BOUND. Uniform in `n`, uniform on any compact `K ⊆ ℂ`,
at ANY parabola depth.** This is the theorem that makes depth free. -/
theorem galQRes_head_integral_bound
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ Chead : ℝ, 0 ≤ Chead ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖∫ t in Set.Ioc (0:ℝ) spikeT0, galQResIntegrand n s t‖ ≤ Chead := by
  obtain ⟨C, hC0, hbd⟩ := galQRes_integrand_short_time_bound
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  obtain ⟨M, hM0, hMK⟩ := exists_nonneg_neg_re_bound K hK hne
  set E : ℝ := Real.exp (M * spikeT0) with hE
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  set A : ℝ := E * (1 / (2 * Real.sqrt Real.pi)) with hA
  have hA0 : (0:ℝ) ≤ A := by rw [hA]; positivity
  have hEC0 : (0:ℝ) ≤ E * C := mul_nonneg hE0.le hC0
  refine ⟨∫ t in Set.Ioc (0:ℝ) spikeT0, (A * (t ^ (-(1:ℝ)/2)) + E * C), ?_, ?_⟩
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have hr : (0:ℝ) ≤ t ^ (-(1:ℝ)/2) := Real.rpow_nonneg ht0.le _
    positivity
  · intro n s hs
    have hdom : IntegrableOn
        (fun t : ℝ => A * (t ^ (-(1:ℝ)/2)) + E * C) (Set.Ioc 0 spikeT0) :=
      dominator_integrableOn spikeT0 hT.le _ _
    refine norm_integral_le_of_norm_le hdom ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht.1
    have htT : t ≤ spikeT0 := ht.2
    have hb := hbd n s t ht0 htT
    have hexp : Real.exp (-s.re * t) ≤ E :=
      exp_neg_re_le M t spikeT0 s.re hM0 (hMK s hs) ht0 htT
    have hfd : freeHeatDiagonal t = 1 / (2 * Real.sqrt Real.pi) * (t ^ (-(1:ℝ)/2)) :=
      freeHeatDiagonal_eq_rpow t ht0
    have hfd0 : (0:ℝ) ≤ freeHeatDiagonal t := freeHeatDiagonal_nonneg t
    calc ‖galQResIntegrand n s t‖
        ≤ Real.exp (-s.re * t) * (freeHeatDiagonal t + C) := hb
      _ ≤ E * (freeHeatDiagonal t + C) :=
          mul_le_mul_of_nonneg_right hexp (by linarith)
      _ = A * (t ^ (-(1:ℝ)/2)) + E * C := by rw [hfd, hA]; ring

#print axioms dominator_integrableOn
#print axioms heatKernelG_continuousOn_Ioc
#print axioms galQRes_continuousOn_Ioc
#print axioms exp_neg_re_le
#print axioms exists_nonneg_neg_re_bound
#print axioms galQRes_integrableOn_head
#print axioms galQRes_head_integral_bound

end RHFormalization
