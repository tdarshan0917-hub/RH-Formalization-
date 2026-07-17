import RHFormalization.ShiftedLaplaceRepRestWitnessStaged
import RHFormalization.ShiftedLaplaceRepRestAtWitness
import RHFormalization.AnalyticWrappers

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem repZpole_rest_analyticAt_witness
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0)
    (hRisoRep : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ ρrep →
      R ≤ dist (polePoint ρ') W.s0)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2))) :
    HolomorphicAtC
      (fun w => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w)) W.s0 := by
  have hLU := repRestPartial_tendstoLocallyUniformlyOn_witnessBall
      W ρrep hρrep_re hρrep_pole R hR hRiso hsum
  have hLUball : TendstoLocallyUniformlyOn
      (fun n s => repRestPartial defaultZeroMultiplicityData ρrep n s)
      (fun s => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 s))
      atTop (Metric.ball W.s0 R) := hLU
  have hdiff : DifferentiableOn ℂ
      (fun s => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 s))
      (Metric.ball W.s0 R) :=
    hLUball.differentiableOn
      (Filter.Eventually.of_forall (fun n =>
        repRestPartial_differentiableOn defaultZeroMultiplicityData ρrep n W.s0 R hRisoRep))
      Metric.isOpen_ball
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) W.s0 (Metric.mem_ball_self hR)

#print axioms repZpole_rest_analyticAt_witness

end
end RHFormalization
