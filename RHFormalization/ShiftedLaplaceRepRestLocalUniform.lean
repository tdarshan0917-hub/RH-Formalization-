import RHFormalization.ShiftedLaplaceRepRestBallConv

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

/--
Convert the witness-ball uniform convergence just banked into the
locally-uniform convergence form needed for the uniform-limit-of-holomorphic
step.

This is the immediate next rung after `repRest_tendstoUniformlyOn_witnessBall`.
-/
theorem repRest_tendstoLocallyUniformlyOn_witnessBall
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1 / 2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso :
      ∀ ρ' : ℂ,
        IsNontrivialZetaZero ρ' →
        ρ' ≠ W.ρ →
        ρ' ≠ 1 - W.ρ →
          2 * R ≤ dist (polePoint ρ') W.s0)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2))) :
    TendstoLocallyUniformlyOn
      (fun (t : Finset RepZeroIndex) x =>
        ∑ ρ ∈ t,
          (if ρ.1 = ρrep then 0 else
            zeroPoleSummand defaultZeroMultiplicityData ρ.1 x))
      (fun x =>
        ∑' ρ : RepZeroIndex,
          (if ρ.1 = ρrep then 0 else
            zeroPoleSummand defaultZeroMultiplicityData ρ.1 x))
      atTop
      (Metric.ball W.s0 R) := by
  have hU :=
    repRest_tendstoUniformlyOn_witnessBall
      W ρrep hρrep_re hρrep_pole R hR hRiso hsum
  exact hU.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall

#print axioms repRest_tendstoLocallyUniformlyOn_witnessBall

end
end RHFormalization
