import RHFormalization.CosBumpIntegralTailSplit
import RHFormalization.PrimePotentialPosition
set_option autoImplicit false
open MeasureTheory Real Set

namespace RHFormalization

/-- Cos-drop for the left tail: `‖cosBumpLeftTail‖ ≤ ∫ gaussBump` over the
same half-line, since `‖cos(·)·gaussBump‖ = ‖cos(·)‖·gaussBump ≤ gaussBump`
(gaussBump > 0, `‖cos‖ ≤ 1`). -/
theorem norm_cosBumpLeftTail_le_gaussBump_tail
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (j : ℝ) :
    ‖cosBumpLeftTail δ q L j‖
      ≤ ∫ u in Iic (0 - Real.log q), gaussBump δ u := by
  rw [cosBumpLeftTail]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hInt_g : IntegrableOn (fun u => gaussBump δ u)
      (Iic (0 - Real.log q)) volume := by
    have hb : (0:ℝ) < 1/(2*δ^2) := by positivity
    have hbase : Integrable (fun u => Real.exp (-(1/(2*δ^2)) * u^2)) :=
      integrable_exp_neg_mul_sq hb
    have hdiv : Integrable
        (fun u => Real.exp (-(1/(2*δ^2)) * u^2) / Real.sqrt (2*Real.pi*δ^2)) :=
      hbase.div_const _
    refine (hdiv.congr ?_).integrableOn
    filter_upwards with u
    unfold gaussBump
    congr 1
    rw [neg_div]
    ring_nf
  have hInt_n : IntegrableOn (fun u => ‖cosBumpFullIntegrand δ q L j u‖)
      (Iic (0 - Real.log q)) volume :=
    (integrable_cosBumpFullIntegrand δ hδ q L j).norm.integrableOn
  apply setIntegral_mono_on hInt_n hInt_g measurableSet_Iic
  intro u _
  unfold cosBumpFullIntegrand
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (gaussBump_pos δ hδ _)]
  have hcos : |Real.cos (j * Real.pi * (u + Real.log q) / L)| ≤ 1 :=
    Real.abs_cos_le_one _
  nlinarith [hcos, gaussBump_pos δ hδ u, abs_nonneg (Real.cos (j * Real.pi * (u + Real.log q) / L))]

end RHFormalization
