import RHFormalization.ShiftedLaplaceRepDenomBound
import RHFormalization.ShiftedLaplaceRepRestLUC
import RHFormalization.ShiftedLaplaceRepEnvelope

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem repRest_tendstoUniformlyOn_ball_of_const
    (ρrep : ℂ) (z0 : ℂ) (R : ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcbound : ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re < 1/2 → ρ ≠ ρrep →
      ∀ s ∈ Metric.closedBall z0 R, c * (1 + ρ.im ^ 2) ≤ ‖zeroPoleDenom ρ s‖)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2))) :
    TendstoUniformlyOn
      (fun (t : Finset RepZeroIndex) x =>
        ∑ ρ ∈ t, (if ρ.1 = ρrep then 0 else
          zeroPoleSummand defaultZeroMultiplicityData ρ.1 x))
      (fun x => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0 else
          zeroPoleSummand defaultZeroMultiplicityData ρ.1 x))
      atTop (Metric.closedBall z0 R) := by
  have hrep : Summable
      ((fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
        (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) ∘ repToFull) :=
    hsum.comp_injective repToFull_injective
  have husummable : Summable (fun ρ : RepZeroIndex =>
      (1 / c) * ((defaultZeroMultiplicityData.mult (repToFull ρ).1 : ℝ)
        / (1 + (repToFull ρ).1.im ^ 2))) :=
    hrep.mul_left (1 / c)
  refine tendstoUniformlyOn_tsum husummable ?_
  intro ρ x hx
  by_cases hr : ρ.1 = ρrep
  · rw [if_pos hr, norm_zero]
    have h1 : (0:ℝ) < 1 + (repToFull ρ).1.im ^ 2 := by positivity
    have hmnn : (0:ℝ) ≤ (defaultZeroMultiplicityData.mult (repToFull ρ).1 : ℝ) := by positivity
    have hcnn : (0:ℝ) ≤ 1 / c := by positivity
    positivity
  · rw [if_neg hr]
    have hρz : IsNontrivialZetaZero ρ.1 := ρ.2.1
    have hρre : ρ.1.re < 1/2 := ρ.2.2
    have hden := hcbound ρ.1 hρz hρre hr x hx
    have h1 : (0:ℝ) < 1 + ρ.1.im ^ 2 := by positivity
    have hnorm : ‖zeroPoleSummand defaultZeroMultiplicityData ρ.1 x‖ =
        (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / ‖zeroPoleDenom ρ.1 x‖ := by
      unfold zeroPoleSummand
      rw [norm_div, Complex.norm_natCast]
    rw [hnorm]
    have hrfl : (repToFull ρ).1 = ρ.1 := rfl
    rw [hrfl]
    have hb : (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / ‖zeroPoleDenom ρ.1 x‖ ≤
        (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (c * (1 + ρ.1.im ^ 2)) := by
      gcongr
    refine hb.trans (le_of_eq ?_)
    field_simp

set_option maxHeartbeats 1000000 in
theorem repRest_tendstoUniformlyOn_witnessBall
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2))) :
    TendstoUniformlyOn
      (fun (t : Finset RepZeroIndex) x =>
        ∑ ρ ∈ t, (if ρ.1 = ρrep then 0 else
          zeroPoleSummand defaultZeroMultiplicityData ρ.1 x))
      (fun x => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0 else
          zeroPoleSummand defaultZeroMultiplicityData ρ.1 x))
      atTop (Metric.closedBall W.s0 R) :=
  repRest_tendstoUniformlyOn_ball_of_const ρrep W.s0 R
    (witnessDenomConst W ρrep hρrep_re hρrep_pole R hR hRiso)
    (witnessDenomConst_pos W ρrep hρrep_re hρrep_pole R hR hRiso)
    (witnessDenomConst_le W ρrep hρrep_re hρrep_pole R hR hRiso)
    hsum

#print axioms repRest_tendstoUniformlyOn_ball_of_const
#print axioms repRest_tendstoUniformlyOn_witnessBall

end
end RHFormalization
