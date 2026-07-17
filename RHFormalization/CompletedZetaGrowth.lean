import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import RHFormalization.CompletedZetaMeromorphic
import RHFormalization.MellinBound

/-!
# Brick B (fragments B1, B2) — toward a crude circle growth bound on `Λ₀`

`Λ₀ = mellin f_modif`, and the Mellin integrand `(x:ℂ)^(s-1) • f x` has norm depending
ONLY on `Re s` (the imaginary part of `s` contributes a unit-modulus phase). Hence
`‖mellin f s‖ ≤ ∫ ‖f x‖ x^(Re s − 1) dx =: M(Re s)`, independent of `Im s`.

B1: integrand norm identity. B2: the `‖mellin‖ ≤ M(Re s)` bound.
B3 (the analytic core, later) bounds `M(σ)` for `σ ∈ [−R, R]` using `f_modif` decay.
-/

namespace RHFormalization
open Complex Real MeasureTheory Set HurwitzZeta

/-- **B1 — Mellin integrand norm identity.** For `x > 0`,
`‖(x:ℂ)^(s-1) • f x‖ = x^(Re s − 1) · ‖f x‖`. The phase from `Im s` cancels in the norm. -/
theorem mellin_integrand_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (s - 1) • f x‖ = x ^ (s.re - 1) * ‖f x‖ := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

#print axioms mellin_integrand_norm

/-- The Hurwitz-even FE pair at `a = 0`, whose `Λ₀/2 = completedRiemannZeta₀`. -/
noncomputable def fePair0 : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair 0

/-- **B3a — exponential tail majorant for the `Λ₀` kernel.**
`f_modif` of the even pair decays exponentially at `+∞`: there exist `C, p > 0` with
`‖fePair0.f_modif x‖ ≤ C · exp(−p·x)` eventually. This is the carried theta-kernel decay,
the engine that will bound the Mellin tail integral (B3b). -/
theorem fePair0_fmodif_exp_decay :
    ∃ p : ℝ, 0 < p ∧ (fePair0.f_modif · ) =O[Filter.atTop] (fun x => Real.exp (-p * x)) := by
  obtain ⟨p, hp, hp'⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub 0
  refine ⟨p, hp, ?_⟩
  -- on atTop (x > 1), f_modif x = f x - f₀ = (evenKernel 0 x - 1 : ℂ)
  have hev : (fePair0.f_modif ·) =ᶠ[Filter.atTop]
      (fun x => ((HurwitzZeta.evenKernel 0 x - (if (0:UnitAddCircle) = 0 then 1 else 0) : ℝ) : ℂ)) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    simp only [fePair0, HurwitzZeta.hurwitzEvenFEPair, WeakFEPair.f_modif, Pi.add_apply,
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx),
      Set.indicator_of_notMem (Set.notMem_Ioo_of_ge hx.le), add_zero,
      Function.comp_apply, Complex.ofReal_sub]
    norm_num
  rw [Asymptotics.isBigO_congr hev (by rfl)]
  -- ‖(real)‖ = |real|, transfer the real isBigO to ℂ
  rw [← Asymptotics.isBigO_norm_left]
  simp only [Complex.norm_real]
  rw [Asymptotics.isBigO_norm_left]
  simpa using hp'

#print axioms fePair0_fmodif_exp_decay

/-- **B3b — the scaled exponential integral as a Gamma value.**
`∫ t in Ioi 0, t^(a-1)·exp(-b·t) = b^(-a)·Γ(a)` for `a, b > 0`. Direct from Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` at `p = 1`. This is the closed form that converts the
Mellin tail bound into a `Γ`-growth statement. -/
theorem integral_rpow_mul_exp_eq_gamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Set.Ioi (0:ℝ), t ^ (a - 1) * Real.exp (-b * t)
      = b ^ (-a) * Real.Gamma a := by
  have hq : (-1:ℝ) < a - 1 := by linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a - 1) (b := b)
    one_pos hq hb
  simp only [Real.rpow_one] at h
  rw [h]
  -- (a-1+1)/1 = a ; b^(-(a-1+1)/1) = b^(-a)
  have e1 : (a - 1 + 1) / 1 = a := by ring
  rw [e1]
  rw [show (-(a - 1 + 1) / 1) = -a by ring]
  ring

#print axioms integral_rpow_mul_exp_eq_gamma

/-- **f_modif is integrable on `Ioc 0 1`** (unweighted), from Mellin convergence at `s = 1`
(`1 > k = 1/2`), where the weight `t^(1-1) = 1`. Needed to discharge the head-bound hypothesis. -/
theorem fePair0_fmodif_integrableOn_Ioi0 :
    MeasureTheory.IntegrableOn fePair0.f_modif (Set.Ioi (0:ℝ)) := by
  -- MellinConvergent f_modif 1 : IntegrableOn (t^(1-1) • f_modif) (Ioi 0); weight t^0 = 1
  have hmc : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif 1 :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin 1).1
  rw [MellinConvergent] at hmc
  have hcongr : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((1:ℂ) - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t)
      (Set.Ioi 0) := hmc
  refine hcongr.congr_fun (fun t ht => ?_) measurableSet_Ioi
  show (t : ℂ) ^ ((1:ℂ) - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t
      = fePair0.f_modif t
  simp only [sub_self, Complex.cpow_zero, one_smul, fePair0]

#print axioms fePair0_fmodif_integrableOn_Ioi0

/-- `‖f_modif‖` integrable on `Ioc 0 T` for any `T` (restriction of the `Ioi 0` integrability). -/
theorem fePair0_fmodif_norm_integrableOn_Ioc0 (T : ℝ) :
    MeasureTheory.IntegrableOn (fun t => ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) T) :=
  (fePair0_fmodif_integrableOn_Ioi0.mono_set Set.Ioc_subset_Ioi_self).norm

#print axioms fePair0_fmodif_norm_integrableOn_Ioc0

theorem fePair0_fmodif_integrableOn_Ioc01 :
    MeasureTheory.IntegrableOn (fun t => ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) 1) :=
  fePair0_fmodif_norm_integrableOn_Ioc0 1

#print axioms fePair0_fmodif_integrableOn_Ioc01

/-- **B3c-head — the near-0 part of the Mellin integral is uniformly bounded.**
For `σ ≥ 2`, on `(0,1]` we have `t^(σ/2-1) ≤ 1`, so the head integral is dominated by the
σ-independent constant `∫ t in Ioc 0 1, ‖f_modif t‖`. -/
theorem fePair0_mellin_head_le {σ : ℝ} (hσ : 2 ≤ σ) :
    ∫ t in Set.Ioc (0:ℝ) 1, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
      ≤ ∫ t in Set.Ioc (0:ℝ) 1, ‖fePair0.f_modif t‖ := by
  have hint : MeasureTheory.IntegrableOn (fun t => ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) 1) :=
    fePair0_fmodif_integrableOn_Ioc01
  have hexp : (0:ℝ) ≤ σ / 2 - 1 := by linarith
  -- weighted integrand is integrable: dominated in norm by ‖f_modif‖
  have hwint : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) 1) := by
    refine hint.mono' ?_ ?_
    · -- a.e. strongly measurable
      apply MeasureTheory.AEStronglyMeasurable.mul _ hint.aestronglyMeasurable
      exact (Real.continuous_rpow_const hexp).aestronglyMeasurable.restrict
    · -- ‖t^(σ/2-1) * ‖f_modif t‖‖ ≤ ‖f_modif t‖ a.e. on Ioc 0 1
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      have htpos : 0 < t := ht.1
      have htle : t ≤ 1 := ht.2
      have hle1 : t ^ (σ / 2 - 1) ≤ 1 := Real.rpow_le_one htpos.le htle hexp
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
          ≤ 1 * ‖fePair0.f_modif t‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)
        _ = ‖fePair0.f_modif t‖ := one_mul _
  apply MeasureTheory.setIntegral_mono_on hwint hint measurableSet_Ioc
  intro t ht
  have htpos : 0 < t := ht.1
  have htle : t ≤ 1 := ht.2
  have hle1 : t ^ (σ / 2 - 1) ≤ 1 := Real.rpow_le_one htpos.le htle hexp
  calc t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
      ≤ 1 * ‖fePair0.f_modif t‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)
    _ = ‖fePair0.f_modif t‖ := one_mul _

#print axioms fePair0_mellin_head_le

/-- **B3c-head over `Ioc 0 T`.** For `σ ≥ 2` and `T ≥ 1`, the weighted head integral over `(0,T]`
is bounded by `max 1 (T^(σ/2-1))` times the constant `∫_{Ioc 0 T} ‖f_modif‖`. The factor is
σ-dependent but `exp(O(σ))` (sub-Gamma), so it is absorbed in the final order bound. -/
theorem fePair0_mellin_head_le_Ioc0T {σ T : ℝ} (hσ : 2 ≤ σ) (hT : 1 ≤ T) :
    ∫ t in Set.Ioc (0:ℝ) T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
      ≤ max 1 (T ^ (σ / 2 - 1)) * ∫ t in Set.Ioc (0:ℝ) T, ‖fePair0.f_modif t‖ := by
  have hexp : (0:ℝ) ≤ σ / 2 - 1 := by linarith
  have hint : MeasureTheory.IntegrableOn (fun t => ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) T) :=
    fePair0_fmodif_norm_integrableOn_Ioc0 T
  set K : ℝ := max 1 (T ^ (σ / 2 - 1)) with hK
  have hK0 : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  -- pointwise sup bound: t^(σ/2-1) ≤ K on (0,T]
  have hsup : ∀ t ∈ Set.Ioc (0:ℝ) T, t ^ (σ / 2 - 1) ≤ K := by
    intro t ht
    have htpos : 0 < t := ht.1
    have htT : t ≤ T := ht.2
    rcases le_or_gt t 1 with h1 | h1
    · exact le_trans (Real.rpow_le_one htpos.le h1 hexp) (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow htpos.le htT hexp) (le_max_right _ _)
  -- weighted integrand integrable on Ioc 0 T
  have hwint : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) T) := by
    refine (hint.const_mul K).mono' ?_ ?_
    · apply MeasureTheory.AEStronglyMeasurable.mul
      · exact (Real.continuous_rpow_const hexp).aestronglyMeasurable.restrict
      · exact hint.aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      have htpos : 0 < t := ht.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
          ≤ K * ‖fePair0.f_modif t‖ := mul_le_mul_of_nonneg_right (hsup t ht) (norm_nonneg _)
        _ = K * ‖fePair0.f_modif t‖ := rfl
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_mono_on hwint (hint.const_mul K) measurableSet_Ioc
  intro t ht
  exact mul_le_mul_of_nonneg_right (hsup t ht) (norm_nonneg _)

#print axioms fePair0_mellin_head_le_Ioc0T


/-- The weighted **norm** integrand `t^(σ-1)·‖f_modif t‖` is integrable on `Ioi 0` for `σ > 1/2`,
obtained from `MellinConvergent f_modif s` (`s.re > k = 1/2`) via the integrand-norm identity. -/
theorem fePair0_weighted_norm_integrableOn_Ioi0 (s : ℂ) :
    MeasureTheory.IntegrableOn
      (fun t => t ^ (s.re - 1) * ‖fePair0.f_modif t‖) (Set.Ioi (0:ℝ)) := by
  -- MellinConvergent is definitionally IntegrableOn (t^(s-1) • f_modif) (Ioi 0)
  have hmc : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t)
      (Set.Ioi 0) :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin s).1
  have hnorm : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖)
      (Set.Ioi 0) := hmc.norm
  refine hnorm.congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact mellin_integrand_norm fePair0.f_modif s (Set.mem_Ioi.mp ht)

#print axioms fePair0_weighted_norm_integrableOn_Ioi0

/-- **B3c-tail — the far tail of the Mellin integral is bounded by a Gamma value.**
From the exponential decay `‖f_modif t‖ ≤ C·exp(-p·t)` (eventually, via `fePair0_fmodif_exp_decay`)
there are `C, p, T > 0` such that for all `σ ≥ 2`,
`∫ t in Ioi T, t^(σ/2-1)·‖f_modif t‖ ≤ C · p^(-σ/2) · Γ(σ/2)`.
This is the Gamma-growing part of the Mellin bound; combined with the bounded head
(`fePair0_mellin_head_le`) and the finite middle piece, it yields the order bound on `Λ₀`. -/
theorem fePair0_mellin_tail_le :
    ∃ C p T : ℝ, 0 < C ∧ 0 < p ∧ 0 < T ∧
      ∀ σ : ℝ, 2 ≤ σ →
        (∫ t in Set.Ioi T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖)
          ≤ C * p ^ (-(σ / 2)) * Real.Gamma (σ / 2) := by
  obtain ⟨p, hp, hObig⟩ := fePair0_fmodif_exp_decay
  obtain ⟨C, hCwith⟩ := hObig.isBigOWith
  -- extract eventual bound ‖f_modif t‖ ≤ C * exp(-p t)
  have hbound := hCwith.bound
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨T0, hT0⟩ := hbound
  set T : ℝ := max T0 1 with hT_def
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC0 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max C 1, p, T, hC0, hp, hTpos, fun σ hσ => ?_⟩
  have hq : (-1:ℝ) < σ / 2 - 1 := by linarith
  -- pointwise: on Ioi T, t^(σ/2-1)*‖f_modif t‖ ≤ (max C 1) * (t^(σ/2-1) * exp(-p t))
  have hpt : ∀ t ∈ Set.Ioi T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
      ≤ (max C 1) * (t ^ (σ / 2 - 1) * Real.exp (-p * t)) := by
    intro t ht
    have htT0 : T0 ≤ t := le_trans (le_max_left _ _) (le_of_lt ht)
    have hfb : ‖fePair0.f_modif t‖ ≤ C * ‖Real.exp (-p * t)‖ := hT0 t htT0
    have hexpnn : ‖Real.exp (-p * t)‖ = Real.exp (-p * t) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hexpnn] at hfb
    have htpos : 0 < t := lt_trans hTpos ht
    have htr_nn : 0 ≤ t ^ (σ / 2 - 1) := Real.rpow_nonneg htpos.le _
    calc t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖
        ≤ t ^ (σ / 2 - 1) * (C * Real.exp (-p * t)) :=
          mul_le_mul_of_nonneg_left hfb htr_nn
      _ ≤ t ^ (σ / 2 - 1) * (max C 1 * Real.exp (-p * t)) := by
          apply mul_le_mul_of_nonneg_left _ htr_nn
          apply mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ = (max C 1) * (t ^ (σ / 2 - 1) * Real.exp (-p * t)) := by ring
  -- integrability of the majorant on Ioi 0 (hence Ioi T)
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ / 2 - 1) * Real.exp (-p * t)) (Set.Ioi (0:ℝ)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ / 2 - 1) (b := p)
      hq le_rfl hp
    simpa [Real.rpow_one] using this
  -- weighted integrand integrable on Ioi T (subset of where f_modif decays); via majorant
  have hweight_int_T : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖) (Set.Ioi T) := by
    refine MeasureTheory.Integrable.mono' (hmaj_int.mono_set (by intro x hx; exact lt_trans hTpos hx)
        |>.const_mul (max C 1)) ?_ ?_
    · -- measurability
      apply MeasureTheory.AEStronglyMeasurable.mul
      · exact (Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ σ/2-1)).aestronglyMeasurable.restrict
      · -- ‖f_modif‖ aesm: f_modif loc integrable, norm of it
        have : MeasureTheory.AEStronglyMeasurable fePair0.f_modif (volume.restrict (Set.Ioi T)) := by
          have hli := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_int
          exact (hli.mono_set (Set.Ioi_subset_Ioi hTpos.le)).aestronglyMeasurable
        exact this.norm
    · -- pointwise: ‖weighted‖ ≤ (max C 1)*(majorant)
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      have hb := hpt t ht
      have htpos : 0 < t := lt_trans hTpos ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb
  calc (∫ t in Set.Ioi T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖)
      ≤ ∫ t in Set.Ioi T, (max C 1) * (t ^ (σ / 2 - 1) * Real.exp (-p * t)) := by
        apply MeasureTheory.setIntegral_mono_on hweight_int_T
          (hmaj_int.mono_set (by intro x hx; exact lt_trans hTpos hx) |>.const_mul (max C 1))
          measurableSet_Ioi hpt
    _ = (max C 1) * ∫ t in Set.Ioi T, t ^ (σ / 2 - 1) * Real.exp (-p * t) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (max C 1) * ∫ t in Set.Ioi (0:ℝ), t ^ (σ / 2 - 1) * Real.exp (-p * t) := by
        apply mul_le_mul_of_nonneg_left _ hC0.le
        apply MeasureTheory.setIntegral_mono_set hmaj_int
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
          have : 0 < t := ht
          positivity
        · exact (Set.Ioi_subset_Ioi hTpos.le).eventuallyLE
    _ = (max C 1) * (p ^ (-(σ / 2)) * Real.Gamma (σ / 2)) := by
        rw [integral_rpow_mul_exp_eq_gamma (by linarith : (0:ℝ) < σ/2) hp]
    _ = (max C 1) * p ^ (-(σ / 2)) * Real.Gamma (σ / 2) := by ring

#print axioms fePair0_mellin_tail_le

/-- **B3c-combine — order bound on `Λ₀ = completedRiemannZeta₀`.**
For `σ = re s ≥ 2`: `‖Λ₀(s)‖ ≤ (max 1 (T^(σ/2-1))·A_T + C·p^(-σ/2)·Γ(σ/2))/2`, where `A_T, C, p, T`
are the (σ-independent) head-constant, tail-constant, decay-rate, and split-point. The RHS is
dominated by `Γ(σ/2)` up to `exp(O(σ))` factors — the circle-growth content (Gap 1). -/
theorem completedZeta0_le_gamma_bound :
    ∃ (A C p T : ℝ), 0 < p ∧ 1 ≤ T ∧ 0 ≤ A ∧
      ∀ s : ℂ, 2 ≤ s.re →
        ‖completedRiemannZeta₀ s‖
          ≤ (max 1 (T ^ (s.re / 2 - 1)) * A + C * p ^ (-(s.re / 2)) * Real.Gamma (s.re / 2)) / 2 := by
  obtain ⟨C, p, T0, hC, hp, hT0, htail⟩ := fePair0_mellin_tail_le
  -- ensure split point ≥ 1
  set T : ℝ := max T0 1 with hTdef
  have hT1 : (1:ℝ) ≤ T := le_max_right _ _
  have hT0T : T0 ≤ T := le_max_left _ _
  -- A_T := ∫ t in Ioc 0 T, ‖f_modif t‖
  set A : ℝ := ∫ t in Set.Ioc (0:ℝ) T, ‖fePair0.f_modif t‖ with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => norm_nonneg _)
  refine ⟨A, C, p, T, hp, hT1, hA0, fun s hs => ?_⟩
  set σ : ℝ := s.re with hσ
  have hσ2 : (2:ℝ) ≤ σ := hs
  -- structural Mellin bound (MellinBound), integrand uses re s / 2
  have hML := RHFormalization.norm_completedRiemannZeta0_le s
  -- the weighted-norm integrand on Ioi 0
  have hwint : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖) (Set.Ioi (0:ℝ)) := by
    have h := fePair0_weighted_norm_integrableOn_Ioi0 (s/2)
    rw [Complex.div_ofNat_re] at h
    simpa [hσ] using h
  -- split ∫_{Ioi 0} = ∫_{Ioc 0 T} + ∫_{Ioi T}
  have hsplit : (∫ t in Set.Ioi (0:ℝ), t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖)
      = (∫ t in Set.Ioc (0:ℝ) T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖)
        + ∫ t in Set.Ioi T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖ := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt (lt_of_lt_of_le one_pos hT1))]
    exact MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hwint.mono_set (fun x hx => hx.1))
      (hwint.mono_set (fun x hx => lt_trans (lt_of_lt_of_le one_pos hT1) (Set.mem_Ioi.mp hx)))
  -- head bound
  have hhead := fePair0_mellin_head_le_Ioc0T (σ := σ) (T := T) hσ2 hT1
  -- tail bound (tail lemma gives Ioi T0; restrict-extend to Ioi T since T ≥ T0)
  have htailT : (∫ t in Set.Ioi T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖)
      ≤ C * p ^ (-(σ / 2)) * Real.Gamma (σ / 2) := by
    refine le_trans ?_ (htail σ hσ2)
    apply MeasureTheory.setIntegral_mono_set
      (hwint.mono_set (fun x hx => lt_trans hT0 (Set.mem_Ioi.mp hx)))
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      have : 0 < t := lt_trans hT0 (Set.mem_Ioi.mp ht)
      positivity
    · exact (Set.Ioi_subset_Ioi hT0T).eventuallyLE
  -- assemble
  calc ‖completedRiemannZeta₀ s‖
      ≤ (∫ t in Set.Ioi (0:ℝ), t ^ (σ / 2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖) / 2 := hML
    _ = (∫ t in Set.Ioi (0:ℝ), t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖) / 2 := rfl
    _ = ((∫ t in Set.Ioc (0:ℝ) T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖)
          + ∫ t in Set.Ioi T, t ^ (σ / 2 - 1) * ‖fePair0.f_modif t‖) / 2 := by rw [hsplit]
    _ ≤ (max 1 (T ^ (σ / 2 - 1)) * A + C * p ^ (-(σ / 2)) * Real.Gamma (σ / 2)) / 2 := by
        apply div_le_div_of_nonneg_right ?_ (by norm_num : (0:ℝ) ≤ 2)
        exact add_le_add (hhead.trans_eq (by rw [hA])) htailT

#print axioms completedZeta0_le_gamma_bound

/-- **Strip bound (critical-strip growth, unconditional).**
For all `s` with `s.re ∈ [1/2, 2]`, `‖completedRiemannZeta₀ s‖ ≤ M` for a single constant `M`
**independent of `Im s`**, because the Mellin integral for `Λ₀` converges on the whole strip
(`f_modif` decays at both ends). No Phragmén–Lindelöf or ζ strip estimate needed. σ-uniform
envelope: on `(0,1]`, `t^(σ/2-1) ≤ t^(-3/4)` (since `σ/2-1 ≥ -3/4` and `t ≤ 1`); on `(1,∞)`,
`t^(σ/2-1) ≤ 1` (since `σ/2-1 ≤ 0` and `t ≥ 1`). -/
theorem completedZeta0_strip_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, (1:ℝ)/2 ≤ s.re → s.re ≤ 2 →
      ‖completedRiemannZeta₀ s‖ ≤ M := by
  -- envelope integrability: t^(-3/4)‖f_modif‖ integrable on Ioi 0 (weighted lemma at s.re=1/4)
  have hAioi : MeasureTheory.IntegrableOn
      (fun t => t ^ (-(3:ℝ)/4) * ‖fePair0.f_modif t‖) (Set.Ioi (0:ℝ)) := by
    have h := fePair0_weighted_norm_integrableOn_Ioi0 ((1:ℂ)/4)
    have hre : ((1:ℂ)/4).re - 1 = -(3:ℝ)/4 := by
      rw [Complex.div_ofNat_re, Complex.one_re]; norm_num
    rw [hre] at h
    exact h
  have hAioc : MeasureTheory.IntegrableOn
      (fun t => t ^ (-(3:ℝ)/4) * ‖fePair0.f_modif t‖) (Set.Ioc (0:ℝ) 1) :=
    hAioi.mono_set Set.Ioc_subset_Ioi_self
  have hBioi : MeasureTheory.IntegrableOn (fun t => ‖fePair0.f_modif t‖) (Set.Ioi (1:ℝ)) :=
    (fePair0_fmodif_integrableOn_Ioi0.mono_set (fun x hx => lt_trans one_pos (Set.mem_Ioi.mp hx))).norm
  set A : ℝ := ∫ t in Set.Ioc (0:ℝ) 1, t ^ (-(3:ℝ)/4) * ‖fePair0.f_modif t‖ with hAdef
  set B : ℝ := ∫ t in Set.Ioi (1:ℝ), ‖fePair0.f_modif t‖ with hBdef
  have hA0 : 0 ≤ A := MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    (fun t ht => mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))
  have hB0 : 0 ≤ B := MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t _ => norm_nonneg _)
  refine ⟨(A + B) / 2, by positivity, fun s hs1 hs2 => ?_⟩
  set σ : ℝ := s.re with hσ
  -- structural Mellin bound
  have hML := RHFormalization.norm_completedRiemannZeta0_le s
  -- the whole-line weighted integrand is integrable (all s)
  have hwint : MeasureTheory.IntegrableOn
      (fun t => t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖) (Set.Ioi (0:ℝ)) := by
    have h := fePair0_weighted_norm_integrableOn_Ioi0 (s/2)
    rw [Complex.div_ofNat_re] at h
    simpa [hσ] using h
  -- split the Mellin integral at 1 and bound each piece by the envelope
  have hunion : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0:ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (le_of_lt one_pos)
  have hsplit : (∫ t in Set.Ioi (0:ℝ), t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖)
      = (∫ t in Set.Ioc (0:ℝ) 1, t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖)
        + ∫ t in Set.Ioi 1, t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖ := by
    rw [← hunion]
    exact MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hwint.mono_set (fun x hx => hx.1))
      (hwint.mono_set (fun x hx => lt_trans one_pos (Set.mem_Ioi.mp hx)))
  -- exponent bounds
  have hexp_lo : -(3:ℝ)/4 ≤ σ/2 - 1 := by rw [hσ] at hs1 ⊢; linarith
  have hexp_hi : σ/2 - 1 ≤ 0 := by rw [hσ] at hs2 ⊢; linarith
  -- head: ∫_(0,1] t^(σ/2-1)‖f‖ ≤ ∫_(0,1] t^(-3/4)‖f‖ = A
  have hhead : (∫ t in Set.Ioc (0:ℝ) 1, t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖) ≤ A := by
    rw [hAdef]
    apply MeasureTheory.setIntegral_mono_on (hwint.mono_set (fun x hx => hx.1)) hAioc measurableSet_Ioc
    intro t ht
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    -- t ≤ 1, exponent σ/2-1 ≥ -3/4 ⟹ t^(σ/2-1) ≤ t^(-3/4)
    exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 hexp_lo
  -- tail: ∫_(1,∞) t^(σ/2-1)‖f‖ ≤ ∫_(1,∞) ‖f‖ = B
  have htail : (∫ t in Set.Ioi (1:ℝ), t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖) ≤ B := by
    rw [hBdef]
    apply MeasureTheory.setIntegral_mono_on
      (hwint.mono_set (fun x hx => lt_trans one_pos (Set.mem_Ioi.mp hx))) hBioi measurableSet_Ioi
    intro t ht
    have ht1 : (1:ℝ) ≤ t := (Set.mem_Ioi.mp ht).le
    calc t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖
        ≤ 1 * ‖fePair0.f_modif t‖ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos ht1 hexp_hi) (norm_nonneg _)
      _ = ‖fePair0.f_modif t‖ := one_mul _
  -- assemble
  calc ‖completedRiemannZeta₀ s‖
      ≤ (∫ t in Set.Ioi (0:ℝ), t ^ (σ/2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖) / 2 := hML
    _ = (∫ t in Set.Ioi (0:ℝ), t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖) / 2 := rfl
    _ = ((∫ t in Set.Ioc (0:ℝ) 1, t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖)
          + ∫ t in Set.Ioi 1, t ^ (σ/2 - 1) * ‖fePair0.f_modif t‖) / 2 := by rw [hsplit]
    _ ≤ (A + B) / 2 := by
        apply div_le_div_of_nonneg_right (add_le_add hhead htail) (by norm_num)

#print axioms completedZeta0_strip_bound

/-- **Symmetry fold.** Via the functional equation `Λ₀(1-s) = Λ₀(s)`, the value at `s` equals the
value at `1-s`; if `Re s ≤ 1/2` then `Re (1-s) ≥ 1/2`. Reduces the left half-plane to the right. -/
theorem completedZeta0_norm_one_sub (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ = ‖completedRiemannZeta₀ (1 - s)‖ := by
  rw [completedRiemannZeta₀_one_sub]

#print axioms completedZeta0_norm_one_sub

/-- `Re (1 - s) = 1 - Re s`; if `Re s ≤ 1/2` then `Re (1 - s) ≥ 1/2`. -/
theorem one_sub_re_ge (s : ℂ) (hs : s.re ≤ (1:ℝ)/2) : (1:ℝ)/2 ≤ (1 - s).re := by
  rw [Complex.sub_re, Complex.one_re]; linarith

#print axioms one_sub_re_ge

/-- **Strip bound extended to `Re ≤ 2` via symmetry.** For all `s` with `s.re ≤ 2`,
`‖Λ₀ s‖ ≤ M`: if `Re s ∈ [1/2, 2]` use the strip bound directly; if `Re s ≤ 1/2`, fold via the
functional equation to `1 - s` (which has `Re ≥ 1/2`), and `Re(1-s) ≤ 2` automatically since
`Re s ≥ -1`... but we need `Re(1-s) ≤ 2` i.e. `Re s ≥ -1`. For `Re s < -1`, `Re(1-s) > 2`, handled
by the Gamma bound elsewhere. So this covers `Re s ∈ [-1, 2]`. -/
theorem completedZeta0_strip_bound_symm :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, (-1:ℝ) ≤ s.re → s.re ≤ 2 →
      ‖completedRiemannZeta₀ s‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := completedZeta0_strip_bound
  refine ⟨M, hM0, fun s hlo hhi => ?_⟩
  rcases le_or_gt ((1:ℝ)/2) s.re with h | h
  · -- Re s ∈ [1/2, 2]: direct strip bound
    exact hM s h hhi
  · -- Re s < 1/2: fold to 1 - s, which has Re ∈ [1/2, 2]
    rw [completedZeta0_norm_one_sub]
    have h1 : (1:ℝ)/2 ≤ (1 - s).re := one_sub_re_ge s (le_of_lt h)
    have h2 : (1 - s).re ≤ 2 := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    exact hM (1 - s) h1 h2

#print axioms completedZeta0_strip_bound_symm

/-- **Gamma bound extended to `Re ≤ -1` via symmetry.** For `s.re ≤ -1`, fold to `1 - s`
(which has `Re ≥ 2`) and apply the right-half Gamma bound. -/
theorem completedZeta0_le_gamma_bound_left :
    ∃ (A C p T : ℝ), 0 < p ∧ 1 ≤ T ∧ 0 ≤ A ∧
      ∀ s : ℂ, s.re ≤ -1 →
        ‖completedRiemannZeta₀ s‖
          ≤ (max 1 (T ^ ((1 - s).re / 2 - 1)) * A
              + C * p ^ (-((1 - s).re / 2)) * Real.Gamma ((1 - s).re / 2)) / 2 := by
  obtain ⟨A, C, p, T, hp, hT, hA, hbound⟩ := completedZeta0_le_gamma_bound
  refine ⟨A, C, p, T, hp, hT, hA, fun s hs => ?_⟩
  rw [completedZeta0_norm_one_sub]
  have h2 : 2 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  exact hbound (1 - s) h2

#print axioms completedZeta0_le_gamma_bound_left

/-- **Crude Gamma upper bound by a factorial.** For `x ≥ 2`, `Γ(x) ≤ (⌈x⌉)!`, since `Γ` is
monotone on `[2,∞)` and `Γ(n+1) = n!`. Used for the (crude, polynomial) growth rate of `log⁺ M(r)`;
sharper Stirling asymptotics are unnecessary for the summability conclusion. -/
theorem Gamma_le_ceil_factorial {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ (Nat.factorial (Nat.ceil x) : ℝ) := by
  have hxceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hceil2 : 2 ≤ Nat.ceil x := by
    have : (2:ℝ) ≤ (Nat.ceil x : ℝ) := le_trans hx hxceil
    exact_mod_cast this
  -- Γ monotone on Ici 2: Γ x ≤ Γ (⌈x⌉)
  have hmono := (Real.Gamma_strictMonoOn_Ici.monotoneOn)
    (Set.mem_Ici.mpr hx)
    (Set.mem_Ici.mpr (le_trans hx hxceil))
    hxceil
  -- Γ (⌈x⌉) = Γ ((⌈x⌉-1) + 1) = (⌈x⌉-1)! ≤ ⌈x⌉!
  have hnat : Real.Gamma (Nat.ceil x : ℝ) = (Nat.factorial (Nat.ceil x - 1) : ℝ) := by
    have h1 : (Nat.ceil x : ℝ) = ((Nat.ceil x - 1 : ℕ) : ℝ) + 1 := by
      have : 1 ≤ Nat.ceil x := le_trans (by norm_num) hceil2
      rw [Nat.cast_sub this]; ring
    rw [h1, Real.Gamma_nat_eq_factorial]
  have hfac : (Nat.factorial (Nat.ceil x - 1) : ℝ) ≤ (Nat.factorial (Nat.ceil x) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le _ _)
  calc Real.Gamma x ≤ Real.Gamma (Nat.ceil x : ℝ) := hmono
    _ = (Nat.factorial (Nat.ceil x - 1) : ℝ) := hnat
    _ ≤ (Nat.factorial (Nat.ceil x) : ℝ) := hfac

#print axioms Gamma_le_ceil_factorial

/-- **Crude polynomial bound on `log Γ`.** For `x ≥ 2`, `log (Γ x) ≤ (x + 1)^2`. From
`Γ(x) ≤ ⌈x⌉!  ≤ ⌈x⌉^⌈x⌉`, so `log Γ(x) ≤ ⌈x⌉ · log ⌈x⌉ ≤ ⌈x⌉ · ⌈x⌉ ≤ (x+1)^2`. This crude
polynomial rate is more than enough for the summability conclusion (`hsum`); no sharp Stirling
asymptotic is needed. -/
theorem log_Gamma_le_sq {x : ℝ} (hx : 2 ≤ x) :
    Real.log (Real.Gamma x) ≤ (x + 1) ^ 2 := by
  set n : ℕ := Nat.ceil x with hn
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hn2 : 2 ≤ n := by exact_mod_cast le_trans hx hxn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  -- Γ x ≤ n!  ≤ n^n
  have hGle : Real.Gamma x ≤ (Nat.factorial n : ℝ) := Gamma_le_ceil_factorial hx
  have hfp : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hGpow : Real.Gamma x ≤ (n : ℝ) ^ n := le_trans hGle hfp
  -- log Γ x ≤ log (n^n) = n * log n
  have hnpos : (0:ℝ) < (n : ℝ) := by positivity
  have hlogpow : Real.log ((n : ℝ) ^ n) = (n : ℝ) * Real.log (n : ℝ) := by
    rw [Real.log_pow]
  have hGpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  have hlogG : Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc Real.log (Real.Gamma x) ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log hGpos hGpow
      _ = (n : ℝ) * Real.log (n : ℝ) := hlogpow
  -- log n ≤ n, so n * log n ≤ n * n = n^2 ≤ (x+1)^2
  have hlogself : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self (le_of_lt hnpos)
  have hnn : (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hlogself (le_of_lt hnpos)
  -- n ≤ x + 1 since ⌈x⌉ < x + 1
  have hnx1 : (n : ℝ) ≤ x + 1 := by
    have := Nat.ceil_lt_add_one (le_trans (by norm_num) hx : (0:ℝ) ≤ x)
    rw [← hn] at this
    linarith
  have hsq : (n : ℝ) * (n : ℝ) ≤ (x + 1) ^ 2 := by
    have hx1 : (0:ℝ) ≤ x + 1 := by linarith
    nlinarith [hnx1, hnpos]
  calc Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) := hlogG
    _ ≤ (n : ℝ) * (n : ℝ) := hnn
    _ ≤ (x + 1) ^ 2 := hsq

#print axioms log_Gamma_le_sq

/-- **Sharp `O(x log x)` bound on `log Γ`.** For `x ≥ 2`, `log Γ(x) ≤ (x+1)·log(x+1)`. -/
theorem log_Gamma_le_mul_log {x : ℝ} (hx : 2 ≤ x) :
    Real.log (Real.Gamma x) ≤ (x + 1) * Real.log (x + 1) := by
  set n : ℕ := Nat.ceil x with hn
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hn2 : 2 ≤ n := by exact_mod_cast le_trans hx hxn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hGle : Real.Gamma x ≤ (Nat.factorial n : ℝ) := Gamma_le_ceil_factorial hx
  have hfp : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hGpow : Real.Gamma x ≤ (n : ℝ) ^ n := le_trans hGle hfp
  have hnpos : (0:ℝ) < (n : ℝ) := by positivity
  have hGpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  have hlogG : Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc Real.log (Real.Gamma x) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hGpos hGpow
      _ = (n : ℝ) * Real.log (n : ℝ) := by rw [Real.log_pow]
  have hnx1 : (n : ℝ) ≤ x + 1 := by
    have := Nat.ceil_lt_add_one (le_trans (by norm_num) hx : (0:ℝ) ≤ x)
    rw [← hn] at this; linarith
  have hx1pos : (0:ℝ) < x + 1 := by linarith
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlog_mono : Real.log (n : ℝ) ≤ Real.log (x + 1) := Real.log_le_log hnpos hnx1
  calc Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) := hlogG
    _ ≤ (x + 1) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hnx1 hlogn_nonneg
    _ ≤ (x + 1) * Real.log (x + 1) := mul_le_mul_of_nonneg_left hlog_mono (le_of_lt hx1pos)

#print axioms log_Gamma_le_mul_log


/-- `Γ(x) ≤ exp((x+1)^2)` for `x ≥ 2`, from `log Γ(x) ≤ (x+1)^2` and positivity of `Γ`. -/
theorem Gamma_le_exp_sq {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 1) ^ 2) := by
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  have hlog : Real.log (Real.Gamma x) ≤ (x + 1) ^ 2 := log_Gamma_le_sq hx
  calc Real.Gamma x = Real.exp (Real.log (Real.Gamma x)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp ((x + 1) ^ 2) := Real.exp_le_exp.mpr hlog

#print axioms Gamma_le_exp_sq

/-- `Γ(x) ≤ exp((x+1)^2)` for `x ≥ 1` (extends `Gamma_le_exp_sq` to the `[1,2)` range, where
`Γ ≤ 1` by convexity with endpoints `Γ(1) = Γ(2) = 1`). -/
theorem Gamma_le_exp_sq_one {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 1) ^ 2) := by
  rcases le_or_gt 2 x with hge2 | hlt2
  · exact Gamma_le_exp_sq hge2
  · have hmem1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
    have hmem2 : (2:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
    have hzIcc : x ∈ Set.Icc (1:ℝ) 2 := ⟨hx, le_of_lt hlt2⟩
    have hle := Real.convexOn_Gamma.le_max_of_mem_Icc hmem1 hmem2 hzIcc
    rw [Real.Gamma_one, Real.Gamma_two, max_self] at hle
    refine le_trans hle ?_
    rw [Real.one_le_exp_iff]; positivity

#print axioms Gamma_le_exp_sq_one

/-- Sharp: `Γ(x) ≤ exp((x+1)·log(x+1))` for `x ≥ 2`. -/
theorem Gamma_le_exp_mul_log {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  have hlog : Real.log (Real.Gamma x) ≤ (x + 1) * Real.log (x + 1) := log_Gamma_le_mul_log hx
  calc Real.Gamma x = Real.exp (Real.log (Real.Gamma x)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp ((x + 1) * Real.log (x + 1)) := Real.exp_le_exp.mpr hlog

#print axioms Gamma_le_exp_mul_log

/-- Sharp `Γ(x) ≤ exp((x+1)·log(x+1))` for `x ≥ 1` (the `[1,2)` range uses `Γ ≤ 1`). -/
theorem Gamma_le_exp_mul_log_one {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
  rcases le_or_gt 2 x with hge2 | hlt2
  · exact Gamma_le_exp_mul_log hge2
  · have hmem1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
    have hmem2 : (2:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
    have hzIcc : x ∈ Set.Icc (1:ℝ) 2 := ⟨hx, le_of_lt hlt2⟩
    have hle := Real.convexOn_Gamma.le_max_of_mem_Icc hmem1 hmem2 hzIcc
    rw [Real.Gamma_one, Real.Gamma_two, max_self] at hle
    refine le_trans hle ?_
    rw [Real.one_le_exp_iff]
    have hx1 : (1:ℝ) ≤ x + 1 := by linarith
    have hlog_nonneg : 0 ≤ Real.log (x + 1) := Real.log_nonneg hx1
    positivity

#print axioms Gamma_le_exp_mul_log_one


/-- Domination: the gamma-tail majorant `≤ exp (K0 (1+N)^2)`. -/
theorem gamma_majorant_le_exp
    {A Cg pg Tg σ N K0 : ℝ} (hpg : 0 < pg) (hTg : 1 ≤ Tg) (hAg : 0 ≤ A)
    (hσ2 : 2 ≤ σ) (hN0 : 0 ≤ N) (hσN : σ / 2 ≤ 1 + N)
    (hK0 : |A| + |Cg| + |Real.log pg| + |Real.log Tg| + 100 ≤ K0) :
    (max 1 (Tg ^ (σ / 2 - 1)) * A + Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)) / 2
      ≤ Real.exp (K0 * (1 + N) ^ 2) := by
  have h1N : (1:ℝ) ≤ 1 + N := by linarith
  have hσ2ge1 : (1:ℝ) ≤ σ / 2 := by linarith
  have hsumN : (1 + N) ≤ (1 + N) ^ 2 := by nlinarith [hN0]
  have hQpos : (0:ℝ) ≤ (1 + N) ^ 2 := by positivity
  -- self ≤ exp helper: for c ≥ 0, c ≤ exp (c * (1+N)^2)
  have self_le_exp : ∀ c : ℝ, 0 ≤ c → c ≤ Real.exp (c * (1 + N) ^ 2) := by
    intro c hc
    have h1 : c ≤ c * (1 + N) ^ 2 := by nlinarith [hc, hsumN, h1N]
    have h2 : c * (1 + N) ^ 2 ≤ Real.exp (c * (1 + N) ^ 2) := by
      have := Real.add_one_le_exp (c * (1 + N) ^ 2); linarith
    linarith
  -- (1) max 1 (Tg^(σ/2-1)) ≤ exp(|log Tg| (1+N)^2)
  have hT1 : max 1 (Tg ^ (σ / 2 - 1)) ≤ Real.exp (|Real.log Tg| * (1 + N) ^ 2) := by
    apply max_le
    · rw [Real.one_le_exp_iff]; positivity
    · rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < Tg)]
      apply Real.exp_le_exp.mpr
      have hlogTg : 0 ≤ Real.log Tg := Real.log_nonneg hTg
      have habs : Real.log Tg ≤ |Real.log Tg| := le_abs_self _
      have hexp_le : σ / 2 - 1 ≤ (1 + N) ^ 2 := by nlinarith [hσN, hsumN]
      have hexp_nn : (0:ℝ) ≤ σ / 2 - 1 := by linarith
      -- log Tg * (σ/2 - 1) ≤ |log Tg| * (1+N)^2
      calc Real.log Tg * (σ / 2 - 1) ≤ |Real.log Tg| * (σ / 2 - 1) :=
            mul_le_mul_of_nonneg_right habs hexp_nn
        _ ≤ |Real.log Tg| * (1 + N) ^ 2 :=
            mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)
  -- (2) pg^(-σ/2) ≤ exp(|log pg| (1+N)^2)
  have hP1 : pg ^ (-(σ / 2)) ≤ Real.exp (|Real.log pg| * (1 + N) ^ 2) := by
    rw [Real.rpow_def_of_pos hpg]
    apply Real.exp_le_exp.mpr
    have hstep : Real.log pg * (-(σ / 2)) ≤ |Real.log pg| * (σ / 2) := by
      have h1 : Real.log pg * (-(σ / 2)) ≤ |Real.log pg * (-(σ / 2))| := le_abs_self _
      rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ/2)] at h1
      exact h1
    refine le_trans hstep ?_
    have h2 : σ / 2 ≤ (1 + N) ^ 2 := le_trans hσN hsumN
    nlinarith [abs_nonneg (Real.log pg), h2]
  -- (3) Γ(σ/2) ≤ exp(4 (1+N)^2)
  have hG1 : Real.Gamma (σ / 2) ≤ Real.exp (4 * (1 + N) ^ 2) := by
    refine le_trans (Gamma_le_exp_sq_one hσ2ge1) (Real.exp_le_exp.mpr ?_)
    have : σ / 2 + 1 ≤ 2 * (1 + N) := by linarith
    nlinarith [this, hN0, hsumN]
  -- A ≤ exp(|A|(1+N)^2), Cg ≤ |Cg| ≤ exp(|Cg|(1+N)^2)
  have hAle : A ≤ Real.exp (|A| * (1 + N) ^ 2) :=
    le_trans (le_abs_self A) (self_le_exp _ (abs_nonneg A))
  have hCle : Cg ≤ Real.exp (|Cg| * (1 + N) ^ 2) :=
    le_trans (le_abs_self Cg) (self_le_exp _ (abs_nonneg Cg))
  -- positivity facts
  have hTgP : (0:ℝ) ≤ max 1 (Tg ^ (σ / 2 - 1)) := le_trans zero_le_one (le_max_left _ _)
  have hPP : (0:ℝ) ≤ pg ^ (-(σ / 2)) := le_of_lt (Real.rpow_pos_of_pos hpg _)
  have hGP : (0:ℝ) ≤ Real.Gamma (σ / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
  -- term 1: T * A ≤ exp((|log Tg| + |A|)(1+N)^2)
  have hterm1 : max 1 (Tg ^ (σ / 2 - 1)) * A
      ≤ Real.exp ((|Real.log Tg| + |A|) * (1 + N) ^ 2) := by
    calc max 1 (Tg ^ (σ / 2 - 1)) * A
        ≤ Real.exp (|Real.log Tg| * (1+N)^2) * Real.exp (|A| * (1+N)^2) :=
          mul_le_mul hT1 hAle hAg (Real.exp_nonneg _)
      _ = Real.exp ((|Real.log Tg| + |A|) * (1 + N) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
  -- term 2: Cg * P * G ≤ exp((|Cg| + |log pg| + 4)(1+N)^2)
  have hterm2 : Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)
      ≤ Real.exp ((|Cg| + |Real.log pg| + 4) * (1 + N) ^ 2) := by
    calc Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)
        ≤ Real.exp (|Cg| * (1+N)^2) * Real.exp (|Real.log pg| * (1+N)^2)
            * Real.exp (4 * (1+N)^2) := by
          apply mul_le_mul (mul_le_mul hCle hP1 hPP (Real.exp_nonneg _)) hG1 hGP
          exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((|Cg| + |Real.log pg| + 4) * (1 + N) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  -- combine: (term1 + term2)/2 ≤ exp(K0 (1+N)^2)
  have hbig1 : (|Real.log Tg| + |A|) * (1 + N) ^ 2 ≤ K0 * (1 + N) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hQpos
    nlinarith [abs_nonneg (Real.log pg), abs_nonneg Cg, hK0]
  have hbig2 : (|Cg| + |Real.log pg| + 4) * (1 + N) ^ 2 ≤ K0 * (1 + N) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hQpos
    nlinarith [abs_nonneg A, abs_nonneg (Real.log Tg), hK0]
  have hE2 : Real.exp ((|Real.log Tg| + |A|) * (1 + N) ^ 2)
      + Real.exp ((|Cg| + |Real.log pg| + 4) * (1 + N) ^ 2)
      ≤ 2 * Real.exp (K0 * (1 + N) ^ 2) := by
    have e1 := Real.exp_le_exp.mpr hbig1
    have e2 := Real.exp_le_exp.mpr hbig2
    linarith
  calc (max 1 (Tg ^ (σ / 2 - 1)) * A + Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)) / 2
      ≤ (Real.exp ((|Real.log Tg| + |A|) * (1 + N) ^ 2)
          + Real.exp ((|Cg| + |Real.log pg| + 4) * (1 + N) ^ 2)) / 2 := by
        apply div_le_div_of_nonneg_right (add_le_add hterm1 hterm2) (by norm_num)
    _ ≤ (2 * Real.exp (K0 * (1 + N) ^ 2)) / 2 := by
        apply div_le_div_of_nonneg_right hE2 (by norm_num)
    _ = Real.exp (K0 * (1 + N) ^ 2) := by ring

#print axioms gamma_majorant_le_exp

/-- **Sharp gamma-tail majorant** `≤ exp(K0·g(N))` where `g(N) = (1+N)(log(2+N)+1) = O(N log N)`.
This is the `O(R log R)` (Riemann–von Mangoldt rate) envelope, replacing the crude `(1+N)^2`. -/
theorem gamma_majorant_le_exp_sharp
    {A Cg pg Tg σ N K0 : ℝ} (hpg : 0 < pg) (hTg : 1 ≤ Tg) (hAg : 0 ≤ A)
    (hσ2 : 2 ≤ σ) (hN0 : 0 ≤ N) (hσN : σ / 2 ≤ 1 + N)
    (hK0 : |A| + |Cg| + |Real.log pg| + |Real.log Tg| + 100 ≤ K0) :
    (max 1 (Tg ^ (σ / 2 - 1)) * A + Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)) / 2
      ≤ Real.exp (K0 * ((1 + N) * (Real.log (2 + N) + 1))) := by
  set g : ℝ := (1 + N) * (Real.log (2 + N) + 1) with hg
  have h1N : (1:ℝ) ≤ 1 + N := by linarith
  have hσ2ge1 : (1:ℝ) ≤ σ / 2 := by linarith
  have hlog2N_nonneg : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith)
  have hlog2N1_ge1 : (1:ℝ) ≤ Real.log (2 + N) + 1 := by linarith
  -- g ≥ 1+N ≥ 1, g ≥ 0
  have hg_ge_1N : (1 + N) ≤ g := by
    rw [hg]; nlinarith [hlog2N_nonneg, h1N]
  have hg_pos : (0:ℝ) ≤ g := by rw [hg]; positivity
  have hg_ge1 : (1:ℝ) ≤ g := le_trans h1N hg_ge_1N
  -- self ≤ exp helper: for c ≥ 0, c ≤ exp (c * g)
  have self_le_exp : ∀ c : ℝ, 0 ≤ c → c ≤ Real.exp (c * g) := by
    intro c hc
    have h1 : c ≤ c * g := by nlinarith [hc, hg_ge1]
    have h2 : c * g ≤ Real.exp (c * g) := by
      have := Real.add_one_le_exp (c * g); linarith
    linarith
  -- (1) max 1 (Tg^(σ/2-1)) ≤ exp(|log Tg| g)
  have hT1 : max 1 (Tg ^ (σ / 2 - 1)) ≤ Real.exp (|Real.log Tg| * g) := by
    apply max_le
    · rw [Real.one_le_exp_iff]; positivity
    · rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < Tg)]
      apply Real.exp_le_exp.mpr
      have habs : Real.log Tg ≤ |Real.log Tg| := le_abs_self _
      have hexp_le : σ / 2 - 1 ≤ g := by nlinarith [hσN, hg_ge_1N]
      have hexp_nn : (0:ℝ) ≤ σ / 2 - 1 := by linarith
      calc Real.log Tg * (σ / 2 - 1) ≤ |Real.log Tg| * (σ / 2 - 1) :=
            mul_le_mul_of_nonneg_right habs hexp_nn
        _ ≤ |Real.log Tg| * g := mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)
  -- (2) pg^(-σ/2) ≤ exp(|log pg| g)
  have hP1 : pg ^ (-(σ / 2)) ≤ Real.exp (|Real.log pg| * g) := by
    rw [Real.rpow_def_of_pos hpg]
    apply Real.exp_le_exp.mpr
    have hstep : Real.log pg * (-(σ / 2)) ≤ |Real.log pg| * (σ / 2) := by
      have h1 : Real.log pg * (-(σ / 2)) ≤ |Real.log pg * (-(σ / 2))| := le_abs_self _
      rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ/2)] at h1
      exact h1
    refine le_trans hstep ?_
    have h2 : σ / 2 ≤ g := le_trans hσN hg_ge_1N
    nlinarith [abs_nonneg (Real.log pg), h2]
  -- (3) Γ(σ/2) ≤ exp(4 g):  Γ(σ/2) ≤ exp((σ/2+1)log(σ/2+1)) ≤ exp(4 g)
  have hG1 : Real.Gamma (σ / 2) ≤ Real.exp (4 * g) := by
    refine le_trans (Gamma_le_exp_mul_log_one hσ2ge1) (Real.exp_le_exp.mpr ?_)
    -- (σ/2+1)·log(σ/2+1) ≤ 4·g
    have hub : σ / 2 + 1 ≤ 2 + N := by linarith
    have hub_pos : (0:ℝ) < σ / 2 + 1 := by linarith
    have hlogmono : Real.log (σ / 2 + 1) ≤ Real.log (2 + N) :=
      Real.log_le_log hub_pos hub
    have hlognn : 0 ≤ Real.log (σ / 2 + 1) := Real.log_nonneg (by linarith)
    -- (σ/2+1) ≤ 2(1+N)
    have hlin : σ / 2 + 1 ≤ 2 * (1 + N) := by linarith
    calc (σ / 2 + 1) * Real.log (σ / 2 + 1)
        ≤ (2 * (1 + N)) * Real.log (2 + N) := by
          apply mul_le_mul hlin hlogmono hlognn (by linarith)
      _ ≤ 4 * g := by rw [hg]; nlinarith [hlog2N_nonneg, h1N]
  have hAle : A ≤ Real.exp (|A| * g) :=
    le_trans (le_abs_self A) (self_le_exp _ (abs_nonneg A))
  have hCle : Cg ≤ Real.exp (|Cg| * g) :=
    le_trans (le_abs_self Cg) (self_le_exp _ (abs_nonneg Cg))
  have hPP : (0:ℝ) ≤ pg ^ (-(σ / 2)) := le_of_lt (Real.rpow_pos_of_pos hpg _)
  have hGP : (0:ℝ) ≤ Real.Gamma (σ / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
  have hterm1 : max 1 (Tg ^ (σ / 2 - 1)) * A
      ≤ Real.exp ((|Real.log Tg| + |A|) * g) := by
    calc max 1 (Tg ^ (σ / 2 - 1)) * A
        ≤ Real.exp (|Real.log Tg| * g) * Real.exp (|A| * g) :=
          mul_le_mul hT1 hAle hAg (Real.exp_nonneg _)
      _ = Real.exp ((|Real.log Tg| + |A|) * g) := by rw [← Real.exp_add]; ring_nf
  have hterm2 : Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)
      ≤ Real.exp ((|Cg| + |Real.log pg| + 4) * g) := by
    calc Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)
        ≤ Real.exp (|Cg| * g) * Real.exp (|Real.log pg| * g) * Real.exp (4 * g) := by
          apply mul_le_mul (mul_le_mul hCle hP1 hPP (Real.exp_nonneg _)) hG1 hGP
          exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((|Cg| + |Real.log pg| + 4) * g) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hbig1 : (|Real.log Tg| + |A|) * g ≤ K0 * g := by
    apply mul_le_mul_of_nonneg_right _ hg_pos
    nlinarith [abs_nonneg (Real.log pg), abs_nonneg Cg, hK0]
  have hbig2 : (|Cg| + |Real.log pg| + 4) * g ≤ K0 * g := by
    apply mul_le_mul_of_nonneg_right _ hg_pos
    nlinarith [abs_nonneg A, abs_nonneg (Real.log Tg), hK0]
  have hE2 : Real.exp ((|Real.log Tg| + |A|) * g)
      + Real.exp ((|Cg| + |Real.log pg| + 4) * g)
      ≤ 2 * Real.exp (K0 * g) := by
    have e1 := Real.exp_le_exp.mpr hbig1
    have e2 := Real.exp_le_exp.mpr hbig2
    linarith
  calc (max 1 (Tg ^ (σ / 2 - 1)) * A + Cg * pg ^ (-(σ / 2)) * Real.Gamma (σ / 2)) / 2
      ≤ (Real.exp ((|Real.log Tg| + |A|) * g)
          + Real.exp ((|Cg| + |Real.log pg| + 4) * g)) / 2 := by
        apply div_le_div_of_nonneg_right (add_le_add hterm1 hterm2) (by norm_num)
    _ ≤ (2 * Real.exp (K0 * g)) / 2 := by
        apply div_le_div_of_nonneg_right hE2 (by norm_num)
    _ = Real.exp (K0 * g) := by ring

#print axioms gamma_majorant_le_exp_sharp


/-- **Global order bound.** `∃ C ≥ 0, ∀ z, ‖Λ₀ z‖ ≤ exp (C (1 + ‖z‖)^2)`.
Finite-order (≤ 2, crude) envelope assembled from the three regime bounds. Consumed by
Jensen's counting lemma to bound zeros in a disk. -/
theorem completedZeta0_order_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
  obtain ⟨M, hM0, hMband⟩ := completedZeta0_strip_bound_symm
  obtain ⟨A, Cg, pg, Tg, hpg, hTg, hAg, hgR⟩ := completedZeta0_le_gamma_bound
  obtain ⟨A', Cg', pg', Tg', hpg', hTg', hAg', hgL⟩ := completedZeta0_le_gamma_bound_left
  -- Use a single, generously large constant; we only need *some* C making the bound hold.
  -- Each regime's bound is ≤ exp(K0 (1+‖z‖)^2) for K0 large. We prove the existence abstractly:
  -- it suffices to find, for each z, a real K_z with ‖Λ₀ z‖ ≤ exp(K_z) and K_z ≤ K0 (1+‖z‖)^2.
  -- Rather than track constants tightly, we bound ‖Λ₀ z‖ by a continuous function and invoke
  -- that the three explicit majorants are each O(exp(poly)). We assemble K0 explicitly.
  have hlogTg_nonneg : 0 ≤ Real.log Tg := Real.log_nonneg hTg
  set K0 : ℝ := |Real.log M| + |A| + |Cg| + |Real.log pg| + |Real.log Tg|
      + |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| + 100 with hK0def
  have hK0pos : 0 ≤ K0 := by rw [hK0def]; positivity
  refine ⟨K0, hK0pos, fun z => ?_⟩
  -- Abbreviations
  set nz : ℝ := ‖z‖ with hnz
  have hnz0 : 0 ≤ nz := norm_nonneg z
  have hre_le : z.re ≤ nz := le_trans (le_abs_self z.re) (by rw [hnz]; exact abs_re_le_norm z)
  have hre_ge : -nz ≤ z.re := by
    have := abs_re_le_norm z
    rw [← hnz] at this
    rw [abs_le] at this; linarith [this.1]
  -- A convenient global lower bound: exp(K0 (1+nz)^2) ≥ 1 and is huge.
  have hexp_ge_one : (1:ℝ) ≤ Real.exp (K0 * (1 + nz) ^ 2) := by
    rw [Real.one_le_exp_iff]; positivity
  -- Target majorant value
  set E : ℝ := Real.exp (K0 * (1 + nz) ^ 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  -- Case split on Re z
  rcases le_or_gt z.re 2 with hle2 | hgt2
  · rcases le_or_gt (-1 : ℝ) z.re with hge | hlt
    · -- BAND: Re z ∈ [-1, 2], ‖Λ₀ z‖ ≤ M ≤ E
      have hb := hMband z hge hle2
      refine le_trans hb ?_
      -- M ≤ exp(K0 (1+nz)^2): since log M ≤ |log M| ≤ K0 ≤ K0(1+nz)^2
      rcases le_or_gt M 1 with hM1 | hM1
      · exact le_trans hM1 hexp_ge_one
      · -- M > 1: log M ≤ |log M| ≤ K0 ≤ K0 (1+nz)^2
        have hlogM_le : Real.log M ≤ K0 * (1 + nz) ^ 2 := by
          have h1 : Real.log M ≤ |Real.log M| := le_abs_self _
          have h2 : |Real.log M| ≤ K0 := by
            rw [hK0def]
            have hrest : (0:ℝ) ≤ |A| + |Cg| + |Real.log pg| + |Real.log Tg|
                + |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| + 100 := by positivity
            linarith
          have h3 : K0 ≤ K0 * (1 + nz) ^ 2 := by
            nlinarith [hK0pos, sq_nonneg nz, hnz0]
          linarith
        calc M = Real.exp (Real.log M) := (Real.exp_log (by linarith)).symm
          _ ≤ E := by rw [hE]; exact Real.exp_le_exp.mpr hlogM_le
    · -- LEFT TAIL: Re z < -1; majorant in σ = (1-z).re
      have hb := hgL z (le_of_lt hlt)
      refine le_trans hb ?_
      have hσ2 : 2 ≤ (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      have hσN : (1 - z).re / 2 ≤ 1 + nz := by
        rw [Complex.sub_re, Complex.one_re]
        have : -z.re ≤ nz := by linarith [hre_ge]
        linarith
      have hKle : |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| + 100 ≤ K0 := by
        rw [hK0def]
        have h1 : (0:ℝ) ≤ |Real.log M| := abs_nonneg _
        have h2 : (0:ℝ) ≤ |A| + |Cg| + |Real.log pg| + |Real.log Tg| := by positivity
        linarith
      exact gamma_majorant_le_exp hpg' hTg' hAg' hσ2 hnz0 hσN hKle
  · -- RIGHT TAIL: Re z > 2; majorant in σ = z.re
    have hb := hgR z (le_of_lt hgt2)
    refine le_trans hb ?_
    have hσ2 : 2 ≤ z.re := le_of_lt hgt2
    have hσN : z.re / 2 ≤ 1 + nz := by linarith [hre_le]
    have hKle : |A| + |Cg| + |Real.log pg| + |Real.log Tg| + 100 ≤ K0 := by
      rw [hK0def]
      have h1 : (0:ℝ) ≤ |Real.log M| := abs_nonneg _
      have h2 : (0:ℝ) ≤ |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| := by positivity
      linarith
    exact gamma_majorant_le_exp hpg hTg hAg hσ2 hnz0 hσN hKle

#print axioms completedZeta0_order_bound

/-- **Sharp global order bound** `∃ C ≥ 0, ∀ z, ‖Λ₀ z‖ ≤ exp(C·(1+‖z‖)(log(2+‖z‖)+1))`.
The `O(R log R)` envelope (Riemann–von Mangoldt rate), replacing the crude `(1+‖z‖)^2`. -/
theorem completedZeta0_order_bound_sharp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C * ((1 + ‖z‖) * (Real.log (2 + ‖z‖) + 1))) := by
  obtain ⟨M, hM0, hMband⟩ := completedZeta0_strip_bound_symm
  obtain ⟨A, Cg, pg, Tg, hpg, hTg, hAg, hgR⟩ := completedZeta0_le_gamma_bound
  obtain ⟨A', Cg', pg', Tg', hpg', hTg', hAg', hgL⟩ := completedZeta0_le_gamma_bound_left
  have hlogTg_nonneg : 0 ≤ Real.log Tg := Real.log_nonneg hTg
  set K0 : ℝ := |Real.log M| + |A| + |Cg| + |Real.log pg| + |Real.log Tg|
      + |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| + 100 with hK0def
  have hK0pos : 0 ≤ K0 := by rw [hK0def]; positivity
  refine ⟨K0, hK0pos, fun z => ?_⟩
  set nz : ℝ := ‖z‖ with hnz
  have hnz0 : 0 ≤ nz := norm_nonneg z
  have hre_le : z.re ≤ nz := le_trans (le_abs_self z.re) (by rw [hnz]; exact abs_re_le_norm z)
  have hre_ge : -nz ≤ z.re := by
    have := abs_re_le_norm z
    rw [← hnz] at this
    rw [abs_le] at this; linarith [this.1]
  -- envelope multiplier
  set gz : ℝ := (1 + nz) * (Real.log (2 + nz) + 1) with hgz
  have hlog2nz_nonneg : 0 ≤ Real.log (2 + nz) := Real.log_nonneg (by linarith)
  have h1nz : (1:ℝ) ≤ 1 + nz := by linarith
  have hgz_ge_1nz : (1 + nz) ≤ gz := by rw [hgz]; nlinarith [hlog2nz_nonneg, h1nz]
  have hgz_ge1 : (1:ℝ) ≤ gz := le_trans h1nz hgz_ge_1nz
  have hgz_pos : (0:ℝ) ≤ gz := by linarith
  have hexp_ge_one : (1:ℝ) ≤ Real.exp (K0 * gz) := by
    rw [Real.one_le_exp_iff]; positivity
  set E : ℝ := Real.exp (K0 * gz) with hE
  rcases le_or_gt z.re 2 with hle2 | hgt2
  · rcases le_or_gt (-1 : ℝ) z.re with hge | hlt
    · -- BAND
      have hb := hMband z hge hle2
      refine le_trans hb ?_
      rcases le_or_gt M 1 with hM1 | hM1
      · exact le_trans hM1 hexp_ge_one
      · have hlogM_le : Real.log M ≤ K0 * gz := by
          have h1 : Real.log M ≤ |Real.log M| := le_abs_self _
          have h2 : |Real.log M| ≤ K0 := by
            rw [hK0def]
            have hrest : (0:ℝ) ≤ |A| + |Cg| + |Real.log pg| + |Real.log Tg|
                + |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| + 100 := by positivity
            linarith
          have h3 : K0 ≤ K0 * gz := by nlinarith [hK0pos, hgz_ge1]
          linarith
        calc M = Real.exp (Real.log M) := (Real.exp_log (by linarith)).symm
          _ ≤ E := by rw [hE]; exact Real.exp_le_exp.mpr hlogM_le
    · -- LEFT TAIL
      have hb := hgL z (le_of_lt hlt)
      refine le_trans hb ?_
      have hσ2 : 2 ≤ (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      have hσN : (1 - z).re / 2 ≤ 1 + nz := by
        rw [Complex.sub_re, Complex.one_re]
        have : -z.re ≤ nz := by linarith [hre_ge]
        linarith
      have hKle : |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| + 100 ≤ K0 := by
        rw [hK0def]
        have h1 : (0:ℝ) ≤ |Real.log M| := abs_nonneg _
        have h2 : (0:ℝ) ≤ |A| + |Cg| + |Real.log pg| + |Real.log Tg| := by positivity
        linarith
      have := gamma_majorant_le_exp_sharp hpg' hTg' hAg' hσ2 hnz0 hσN hKle
      rw [← hgz] at this
      exact this
  · -- RIGHT TAIL
    have hb := hgR z (le_of_lt hgt2)
    refine le_trans hb ?_
    have hσ2 : 2 ≤ z.re := le_of_lt hgt2
    have hσN : z.re / 2 ≤ 1 + nz := by linarith [hre_le]
    have hKle : |A| + |Cg| + |Real.log pg| + |Real.log Tg| + 100 ≤ K0 := by
      rw [hK0def]
      have h1 : (0:ℝ) ≤ |Real.log M| := abs_nonneg _
      have h2 : (0:ℝ) ≤ |A'| + |Cg'| + |Real.log pg'| + |Real.log Tg'| := by positivity
      linarith
    have := gamma_majorant_le_exp_sharp hpg hTg hAg hσ2 hnz0 hσN hKle
    rw [← hgz] at this
    exact this

#print axioms completedZeta0_order_bound_sharp


/-- `Λ₀(2) = (π - 3)/6 ≠ 0`. Concrete nonzero point for Jensen's center. -/
theorem completedZeta0_ne_zero_at_two :
    completedRiemannZeta₀ 2 ≠ 0 := by
  -- Gammaℝ 2 = π^(-1) * Γ(1) = π⁻¹
  have he1 : (-2 / 2 : ℂ) = -1 := by norm_num
  have he2 : (2 / 2 : ℂ) = 1 := by norm_num
  have hGammaR2 : Complex.Gammaℝ 2 = (π : ℂ)⁻¹ := by
    rw [Complex.Gammaℝ_def, he1, he2, Complex.cpow_neg_one, Complex.Gamma_one, mul_one]
  have hGammaR2_ne : Complex.Gammaℝ 2 ≠ 0 := by
    rw [hGammaR2]
    simp [Real.pi_ne_zero]
  -- Λ(2) = ζ 2 * Gammaℝ 2 = (π²/6) * π⁻¹ = π/6
  have hLam2 : completedRiemannZeta 2 = (π : ℂ) / 6 := by
    have hdef := riemannZeta_def_of_ne_zero (s := 2) (by norm_num)
    have hLam : completedRiemannZeta 2 = riemannZeta 2 * Complex.Gammaℝ 2 := by
      rw [hdef, div_mul_cancel₀ _ hGammaR2_ne]
    rw [hLam, riemannZeta_two, hGammaR2]
    have hpne : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  -- Λ₀ 2 = Λ 2 + 1/2  (since Λ 2 = Λ₀ 2 - 1/2 - 1/(1-2) = Λ₀ 2 - 1/2 + 1)
  have hLam0 : completedRiemannZeta₀ 2 = ((π : ℂ) - 3) / 6 := by
    have heq := completedRiemannZeta_eq 2
    have hstep : completedRiemannZeta₀ 2 = completedRiemannZeta 2 - 1/2 := by
      rw [heq]; ring_nf
    rw [hstep, hLam2]; ring
  rw [hLam0]
  intro hcontra
  rw [div_eq_zero_iff] at hcontra
  rcases hcontra with h | h
  · rw [sub_eq_zero] at h
    have hr : (π : ℝ) = 3 := by exact_mod_cast h
    linarith [Real.pi_gt_three]
  · norm_num at h

#print axioms completedZeta0_ne_zero_at_two


end RHFormalization
