import RHFormalization.GalerkinHeadNormalFamily
import RHFormalization.GalerkinHeadHolo
import RHFormalization.GalerkinHeadIntegralBound
import Mathlib

/-!
# GalerkinHeadSectorBounds — the B-head and F-head, separately bounded

ROUTE CARD
1. Target: `‖∫_{Ioc 0 t₀} galBIntegrand n s‖ ≤ C(K)` and the same for `galFIntegrand`,
   uniformly in `n`, on every compact `K ⊆ ℂ`. No half-plane, no depth condition.
2. Objects: `galB_integrand_short_time_bound` (banked), `galF_integrand_norm_le`
   (banked), `exp_neg_re_le` (banked clamp), `freeHeatDiagonal_eq_rpow` (banked),
   `intervalIntegrable_rpow_neg_half` (banked).
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.KEY-FORM, sectorwise.
7. Consumer: reduces `DBFFO3ParabolaDepthHstar` to a B-TAIL statement.

WHY THE B-HEAD BOUND IS NOT O3 IN DISGUISE. Its dominator is a CONSTANT: the
`(4πt)^{-1/2}` prefactor was already absorbed by `sqrt_inv_mul_exp_neg_div_le`
inside `spike_sum_short_time_bound`, whose statement carries no `s`, no `δ`, and
no half-plane. At short time the Gaussian `e^{-center²/(4t)}` kills every prime
regardless of where `s` sits, so the bound survives `δ → 0`. Contrast the B-TAIL,
where for `t ≥ t₀` the Gaussian tends to `1` and the prime mass
`∑_{q ≤ e^{admR n}} Λ(q)/√q ≍ 2 e^{admR n /2}` diverges; there the bound at depth
IS `DBFFO3ParabolaDepthHstar` (via `B_sub_compensator_eq` +
`galerkin_B_stage_eq_vonMangoldt_partial_sum`).

WHAT THIS BUYS, EXACTLY. On RHP(0), `B_stage = B-head + B-tail`. This file bounds
the B-head uniformly in `n` at any depth. Therefore

    DBFFO3ParabolaDepthHstar  ⟺  the B-TAIL is bounded uniformly in `n` at depth.

One sector removed from O3's surface. O3 itself is untouched and remains the single
open obligation of the chain.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory
open scoped BigOperators

/-- **THE B-HEAD IS `n`-UNIFORMLY BOUNDED.** Constant dominator; no depth condition. -/
theorem galBHead_uniform_bound (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖∫ t in Set.Ioc (0:ℝ) spikeT0, galBIntegrand n s t‖ ≤ C := by
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  obtain ⟨Cspk, hC0, hbd⟩ := galB_integrand_short_time_bound
  obtain ⟨M, hM0, hMK⟩ := exists_nonneg_neg_re_bound K hK hne
  set E : ℝ := Real.exp (M * spikeT0) with hE
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  refine ⟨∫ _t in Set.Ioc (0:ℝ) spikeT0, (E * Cspk), ?_, ?_⟩
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    intro t _
    exact mul_nonneg hE0.le hC0
  · intro n s hs
    have hdom : IntegrableOn (fun _ : ℝ => E * Cspk) (Set.Ioc (0:ℝ) spikeT0) volume :=
      Continuous.integrableOn_Ioc continuous_const
    refine norm_integral_le_of_norm_le hdom ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht.1
    have htT : t ≤ spikeT0 := ht.2
    have hb := hbd n s t ht0 htT
    have hexp : Real.exp (-s.re * t) ≤ E :=
      exp_neg_re_le M t spikeT0 s.re hM0 (hMK s hs) ht0 htT
    calc ‖galBIntegrand n s t‖
        ≤ Real.exp (-s.re * t) * Cspk := hb
      _ ≤ E * Cspk := mul_le_mul_of_nonneg_right hexp hC0

/-- **THE F-HEAD IS `n`-UNIFORMLY BOUNDED.** The `t^{-1/2}` survives here, and is
integrable at `0`. -/
theorem galFHead_uniform_bound (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖∫ t in Set.Ioc (0:ℝ) spikeT0, galFIntegrand n s t‖ ≤ C := by
  have hT : (0:ℝ) < spikeT0 := spikeT0_pos
  obtain ⟨M, hM0, hMK⟩ := exists_nonneg_neg_re_bound K hK hne
  set E : ℝ := Real.exp (M * spikeT0) with hE
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  set A : ℝ := E * (1 / (2 * Real.sqrt Real.pi)) with hA
  have hA0 : (0:ℝ) ≤ A := by rw [hA]; positivity
  refine ⟨∫ t in Set.Ioc (0:ℝ) spikeT0, (A * (t ^ (-(1:ℝ)/2))), ?_, ?_⟩
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have hr : (0:ℝ) ≤ t ^ (-(1:ℝ)/2) := Real.rpow_nonneg ht0.le _
    positivity
  · intro n s hs
    have hdom : IntegrableOn (fun t : ℝ => A * (t ^ (-(1:ℝ)/2)))
        (Set.Ioc (0:ℝ) spikeT0) volume := by
      have h1 := intervalIntegrable_rpow_neg_half spikeT0
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le] at h1
      exact h1.const_mul _
    refine norm_integral_le_of_norm_le hdom ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht.1
    have htT : t ≤ spikeT0 := ht.2
    have hF := galF_integrand_norm_le n s t ht0
    have hexp : Real.exp (-s.re * t) ≤ E :=
      exp_neg_re_le M t spikeT0 s.re hM0 (hMK s hs) ht0 htT
    have hfd : freeHeatDiagonal t = 1 / (2 * Real.sqrt Real.pi) * (t ^ (-(1:ℝ)/2)) :=
      freeHeatDiagonal_eq_rpow t ht0
    have hfd0 : (0:ℝ) ≤ freeHeatDiagonal t := freeHeatDiagonal_nonneg t
    calc ‖galFIntegrand n s t‖
        ≤ Real.exp (-s.re * t) * freeHeatDiagonal t := hF
      _ ≤ E * freeHeatDiagonal t := mul_le_mul_of_nonneg_right hexp hfd0
      _ = A * (t ^ (-(1:ℝ)/2)) := by rw [hfd, hA]; ring

#print axioms galBHead_uniform_bound
#print axioms galFHead_uniform_bound

end RHFormalization
