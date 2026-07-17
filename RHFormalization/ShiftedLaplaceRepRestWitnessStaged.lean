import RHFormalization.ShiftedLaplaceRepRestLocalUniform

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

/--
Staged witness-ball convergence for the rest series.

This is the same bridge pattern as `repRest_luc`, but on the witness ball:
Finset-net convergence + `repSubtypeStage_tendsto`
gives ℕ-staged convergence of `repRestPartial`.

This is the theorem needed before applying the existing
`repRestPartial_differentiableOn` to get analyticity at the witness.
-/
theorem repRestPartial_tendstoLocallyUniformlyOn_witnessBall
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
      (fun n s => repRestPartial defaultZeroMultiplicityData ρrep n s)
      (fun s =>
        ∑' ρ : RepZeroIndex,
          (if ρ.1 = ρrep then 0 else
            zeroPoleSummand defaultZeroMultiplicityData ρ.1 s))
      atTop
      (Metric.ball W.s0 R) := by
  have hU :=
    repRest_tendstoUniformlyOn_witnessBall
      W ρrep hρrep_re hρrep_pole R hR hRiso hsum
  have hcomp := tendstoUniformlyOn_index_comp hU repSubtypeStage_tendsto
  have hfinal : TendstoUniformlyOn
      (fun n s => repRestPartial defaultZeroMultiplicityData ρrep n s)
      (fun s =>
        ∑' ρ : RepZeroIndex,
          (if ρ.1 = ρrep then 0 else
            zeroPoleSummand defaultZeroMultiplicityData ρ.1 s))
      atTop
      (Metric.closedBall W.s0 R) := by
    refine hcomp.congr ?_
    filter_upwards with n
    intro x _
    rfl
  exact hfinal.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall

#print axioms repRestPartial_tendstoLocallyUniformlyOn_witnessBall

end
end RHFormalization
