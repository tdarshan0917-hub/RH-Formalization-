import RHFormalization.ShiftedLaplaceRepRestLUC
import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.ShiftedLaplaceRepHZpp
import RHFormalization.PairPoleIsolation
import Mathlib.Analysis.Complex.RemovableSingularity

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

theorem repRest_eq_full_sub_summand
    (M : ZeroMultiplicityData) (ρrep : ℂ)
    (ρ0 : RepZeroIndex) (hρ0 : ρ0.1 = ρrep) (w : ℂ)
    (hw : Summable (fun ρ : RepZeroIndex => zeroPoleSummand M ρ.1 w)) :
    ZpoleRepSeriesExcept M ρrep w
      = ZpoleRepSeries M w - zeroPoleSummand M ρrep w := by
  classical
  unfold ZpoleRepSeriesExcept ZpoleRepSeries
  rw [hw.tsum_eq_add_tsum_ite ρ0]
  have hite : (∑' ρ : RepZeroIndex, (if ρ = ρ0 then 0 else zeroPoleSummand M ρ.1 w))
      = ∑' ρ : RepZeroIndex, (if ρ.1 = ρrep then 0 else zeroPoleSummand M ρ.1 w) := by
    apply tsum_congr
    intro ρ
    by_cases h : ρ = ρ0
    · simp [h, hρ0]
    · have hne : ρ.1 ≠ ρrep := by
        intro hc; exact h (Subtype.ext (hc.trans hρ0.symm))
      rw [if_neg h, if_neg hne]
  rw [hite, hρ0]; ring

#print axioms repRest_eq_full_sub_summand

theorem repRest_analyticAt_nonpole
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M) (ρrep : ℂ)
    (x : ℂ) (hxΩ : x ∈ Ω) (hx : x ∉ ZeroPoleSet) :
    AnalyticAt ℂ (ZpoleRepSeriesExcept M ρrep) x := by
  obtain ⟨r, hr, hiso⟩ := nonpole_isolated x hxΩ hx
  obtain ⟨ε, hε, hball⟩ :
      ∃ ε > 0, Metric.closedBall x ε ⊆ Ω :=
    (Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_Omega_proved.mem_nhds hxΩ)).imp (fun ε h => ⟨h.1, h.2⟩)
  set r' : ℝ := min (r / 2) ε with hr'def
  have hr'pos : 0 < r' := lt_min (by linarith) hε
  have hr'lt : r' < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hballΩ : Metric.closedBall x r' ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hball
  have hKavoid : ∀ s ∈ Metric.closedBall x r', s ∉ ZeroPoleSet := by
    intro s hs hmem
    obtain ⟨ρ', hρ', hps⟩ := hmem
    rw [Metric.mem_closedBall] at hs
    have hd := hiso ρ' hρ'
    rw [hps] at hs
    linarith
  have hisoRest : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ ρrep →
      r ≤ dist (polePoint ρ') x := fun ρ' h1 _ => hiso ρ' h1
  have hUnif : TendstoUniformlyOn
      (fun n s => repRestPartial M ρrep n s)
      (ZpoleRepSeriesExcept M ρrep) Filter.atTop (Metric.closedBall x r') :=
    tendstoUniformlyOn_of_tlu_isCompact
      (repRest_luc M D ρrep
        ⟨Metric.closedBall x r', isCompact_closedBall _ _, hballΩ, hKavoid⟩)
      (isCompact_closedBall _ _)
  have h1 : TendstoLocallyUniformlyOn
      (fun n s => repRestPartial M ρrep n s)
      (ZpoleRepSeriesExcept M ρrep) Filter.atTop (Metric.ball x r') :=
    hUnif.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have h2 : DifferentiableOn ℂ (ZpoleRepSeriesExcept M ρrep) (Metric.ball x r') :=
    h1.differentiableOn
      (Filter.Eventually.of_forall (fun n =>
        (repRestPartial_differentiableOn M ρrep n x r hisoRest).mono
          (Metric.ball_subset_ball hr'lt.le)))
      Metric.isOpen_ball
  exact (h2.analyticOnNhd Metric.isOpen_ball) x (Metric.mem_ball_self hr'pos)

#print axioms repRest_analyticAt_nonpole

end
end RHFormalization
