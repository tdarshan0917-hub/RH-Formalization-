import RHFormalization.ShiftedLaplaceRepHZpp
import RHFormalization.ShiftedLaplaceRepRestAtWitnessHolo
import RHFormalization.ShiftedLaplaceRepZpoleResidue
import RHFormalization.ShiftedLaplaceRepSummable
import RHFormalization.PairPoleIsolation
import RHFormalization.XiSummability

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

/-- Rep-index-restricted differentiability of the rest partial sum. Identical to
`repRestPartial_differentiableOn` but with the isolation hypothesis quantified
over rep-indices (`ρ'.re < 1/2`) only — which is the satisfiable form, since the
unsummed reflection partner `1 - ρrep` (with `re > 1/2`) is never touched. -/
theorem repRestPartial_differentiableOn_repIndex
    (ρrep : ℂ) (n : ℕ) (x : ℂ) (r : ℝ)
    (hiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ'.re < 1/2 → ρ' ≠ ρrep →
      r ≤ dist (polePoint ρ') x) :
    DifferentiableOn ℂ
      (fun s => repRestPartial defaultZeroMultiplicityData ρrep n s)
      (Metric.ball x r) := by
  unfold repRestPartial
  have hterm : ∀ ρ' ∈ repSubtypeStage n,
      DifferentiableOn ℂ
        (fun s => if ρ'.1 = ρrep then 0
          else zeroPoleSummand defaultZeroMultiplicityData ρ'.1 s)
        (Metric.ball x r) := by
    intro ρ' _
    by_cases hr : ρ'.1 = ρrep
    · simp only [hr, if_pos]
      exact differentiableOn_const 0
    · simp only [if_neg hr]
      have hz' : IsNontrivialZetaZero ρ'.1 := ρ'.2.1
      have hre' : ρ'.1.re < 1/2 := ρ'.2.2
      intro s hs
      have hden : zeroPoleDenom ρ'.1 s ≠ 0 := by
        have hd : zeroPoleDenom ρ'.1 s = s - polePoint ρ'.1 := by
          unfold zeroPoleDenom polePoint; ring
        rw [hd, sub_ne_zero]
        intro hcontra
        have hdist := hiso ρ'.1 hz' hre' hr
        rw [← hcontra] at hdist
        rw [Metric.mem_ball] at hs
        linarith [dist_comm s x ▸ hs]
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold zeroPoleSummand zeroPoleDenom
      unfold zeroPoleDenom at hden
      first
        | exact (differentiableAt_const _).div
            (differentiableAt_id'.add (differentiableAt_const _)) hden
        | exact (differentiableAt_const _).div
            (differentiableAt_id.add (differentiableAt_const _)) hden
  have hsum := DifferentiableOn.sum hterm
  have heq : (∑ i ∈ repSubtypeStage n,
        fun s => if i.1 = ρrep then 0
          else zeroPoleSummand defaultZeroMultiplicityData i.1 s)
      = (fun s => ∑ ρ ∈ repSubtypeStage n,
        if ρ.1 = ρrep then 0
          else zeroPoleSummand defaultZeroMultiplicityData ρ.1 s) := by
    funext s
    rw [Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

/-- Corrected witness rest-analyticity: rest of the rep-series is holomorphic at
the witness, using the SATISFIABLE pair-exclusion isolation. -/
theorem repZpole_rest_analyticAt_witness_satisfiable
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0)
    (hRisoRep : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ'.re < 1/2 → ρ' ≠ ρrep →
      R ≤ dist (polePoint ρ') W.s0)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2))) :
    HolomorphicAtC
      (fun w => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0
          else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w)) W.s0 := by
  have hLU := repRestPartial_tendstoLocallyUniformlyOn_witnessBall
      W ρrep hρrep_re hρrep_pole R hR hRiso hsum
  have hdiff : DifferentiableOn ℂ
      (fun s => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0
          else zeroPoleSummand defaultZeroMultiplicityData ρ.1 s))
      (Metric.ball W.s0 R) :=
    hLU.differentiableOn
      (Filter.Eventually.of_forall (fun n =>
        repRestPartial_differentiableOn_repIndex ρrep n W.s0 R hRisoRep))
      Metric.isOpen_ball
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) W.s0 (Metric.mem_ball_self hR)

#print axioms repRestPartial_differentiableOn_repIndex
#print axioms repZpole_rest_analyticAt_witness_satisfiable

end
end RHFormalization
