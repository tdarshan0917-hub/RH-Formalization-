import RHFormalization.DecodedAdmissibleLocalAnchor
import RHFormalization.AdmissibleWeightNonneg
import Mathlib

/-!
# DecodedAnchorDischarge — Lemma D.ADM-NET step 1, unconditional at live δ

Discharges the five bump/weight hypotheses of `DecodedAdmissibleLocalAnchor`
from the literal `gaussBump` definition:
  `gaussBump δ x = exp(-x²/(2δ²)) / √(2πδ²)`.
Note the peak is `1/√(2πδ²)`, so `gaussBump δ ≤ 1` requires `1 ≤ 2πδ²`;
this holds at the live `δ = 1` since `2π > 1`.

Endpoints (NO hypotheses):
- `decodedAnchor_integrand_integrable_live` : M(R) integrand integrable,
  every R, every coupling c ≥ 0 — the manuscript's "M(R) < ∞";
- `decodedAnchor_window_bound_live` : M(R)/(2·max(L0, M(R))) ≤ 1 —
  the manuscript's "then choose L", schedule-preserving.
-/

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory

theorem gaussBump_nonneg_any (δ y : ℝ) : 0 ≤ gaussBump δ y := by
  unfold gaussBump
  exact div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

theorem gaussBump_le_one_of_peak
    (δ : ℝ) (hδ : 1 ≤ 2 * Real.pi * δ ^ 2) (y : ℝ) :
    gaussBump δ y ≤ 1 := by
  unfold gaussBump
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * δ ^ 2) := by
    have h := Real.sqrt_le_sqrt hδ
    rwa [Real.sqrt_one] at h
  have hpos : 0 < Real.sqrt (2 * Real.pi * δ ^ 2) :=
    lt_of_lt_of_le one_pos hsqrt
  rw [div_le_one hpos]
  have hexp : Real.exp (-y ^ 2 / (2 * δ ^ 2)) ≤ 1 := by
    have harg : -y ^ 2 / (2 * δ ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg y))
        (by positivity)
    calc Real.exp (-y ^ 2 / (2 * δ ^ 2))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr harg
      _ = 1 := Real.exp_zero
  exact hexp.trans hsqrt

theorem gaussBump_continuous_any (δ : ℝ) : Continuous (gaussBump δ) := by
  unfold gaussBump
  exact (Real.continuous_exp.comp
    (((continuous_pow 2).neg).div_const _)).div_const _

theorem gaussBump_measurable_any (δ : ℝ) : Measurable (gaussBump δ) :=
  (gaussBump_continuous_any δ).measurable

theorem gaussBump_integrable_any (δ : ℝ) (hδ : 0 < δ) :
    Integrable (gaussBump δ) volume := by
  unfold gaussBump
  have hb : (0 : ℝ) < 1 / (2 * δ ^ 2) := by positivity
  have hfun :
      (fun x : ℝ => Real.exp (-x ^ 2 / (2 * δ ^ 2))
        / Real.sqrt (2 * Real.pi * δ ^ 2))
      = fun x : ℝ => Real.exp (-(1 / (2 * δ ^ 2)) * x ^ 2)
        / Real.sqrt (2 * Real.pi * δ ^ 2) := by
    funext x
    congr 1
    ring_nf
  rw [hfun]
  exact (integrable_exp_neg_mul_sq hb).div_const _

theorem one_le_two_pi_one_sq : (1 : ℝ) ≤ 2 * Real.pi * 1 ^ 2 := by
  have h := Real.pi_gt_three
  nlinarith

/-- **M(R) < ∞, unconditional (live δ = 1).** Integrand of the exact
D.ADM anchor is integrable at every finite cutoff R and every fixed
coupling c = C*·t0 ≥ 0. Lemma D.ADM-NET, step 1. -/
theorem decodedAnchor_integrand_integrable_live
    (R c : ℝ) (hc : 0 ≤ c) :
    Integrable
      (fun u => Real.exp (c * decodedAdmissibleLocalMajorant 1 R u)
        - 1 - c * decodedAdmissibleLocalMajorant 1 R u) volume :=
  decodedLocalAnchor_integrand_integrable 1 R c hc
    (gaussBump_nonneg_any 1)
    (gaussBump_le_one_of_peak 1 one_le_two_pi_one_sq)
    (gaussBump_measurable_any 1)
    (gaussBump_integrable_any 1 one_pos)
    ppWeightReal_nonneg

theorem decodedAnchor_nonneg_live (R c : ℝ) (hc : 0 ≤ c) :
    0 ≤ decodedAdmissibleLocalAnchor 1 R c :=
  decodedAdmissibleLocalAnchor_nonneg 1 R c hc
    (gaussBump_nonneg_any 1) ppWeightReal_nonneg

/-- **The D.ADM window inequality, unconditional (live δ = 1).**
"Fix R, then choose L := max(L0, M(R))": M(R)/(2L) ≤ 1, with L0 ≤ L so
every banked lower bound on the window survives. Lemma D.ADM-NET, step 2. -/
theorem decodedAnchor_window_bound_live
    (R c L0 : ℝ) (hc : 0 ≤ c) (hL0 : 1 ≤ L0) :
    decodedAdmissibleLocalAnchor 1 R c
      / (2 * max L0 (decodedAdmissibleLocalAnchor 1 R c)) ≤ 1 :=
  decodedAdmissibleLocalAnchor_window_bound 1 R c L0 hc hL0
    (gaussBump_nonneg_any 1) ppWeightReal_nonneg

#print axioms decodedAnchor_integrand_integrable_live
#print axioms decodedAnchor_nonneg_live
#print axioms decodedAnchor_window_bound_live

end RHFormalization
