import RHFormalization.ShiftedLaplaceRepLUC
import RHFormalization.MeromorphyAssembly

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

theorem repPartial_differentiableOn
    (M : ZeroMultiplicityData) (n : ℕ) (x : ℂ) (r : ℝ)
    (hiso : ∀ ρ : ℂ, IsNontrivialZetaZero ρ → r ≤ dist (polePoint ρ) x) :
    DifferentiableOn ℂ
      (fun s => repZeroPolePartial M n s)
      (Metric.ball x r) := by
  unfold repZeroPolePartial
  have hterm : ∀ ρ' ∈ repSubtypeStage n,
      DifferentiableOn ℂ (fun s => zeroPoleSummand M ρ'.1 s)
        (Metric.ball x r) := by
    intro ρ' _
    have hz' : IsNontrivialZetaZero ρ'.1 := ρ'.2.1
    intro s hs
    have hden : zeroPoleDenom ρ'.1 s ≠ 0 := by
      have hd : zeroPoleDenom ρ'.1 s = s - polePoint ρ'.1 := by
        unfold zeroPoleDenom polePoint; ring
      rw [hd, sub_ne_zero]
      intro hcontra
      have hdist := hiso ρ'.1 hz'
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
  have heq : (∑ i ∈ repSubtypeStage n, fun s => zeroPoleSummand M (i.1) s)
      = (fun s => ∑ ρ ∈ repSubtypeStage n, zeroPoleSummand M (ρ.1) s) := by
    funext s
    rw [Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

theorem repZpole_analyticAt_nonpole
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M)
    (x : ℂ) (hxΩ : x ∈ Ω) (hx : x ∉ ZeroPoleSet) :
    AnalyticAt ℂ (ZpoleRepSeries M) x := by
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
  have hUnif : TendstoUniformlyOn
      (fun n s => repZeroPolePartial M n s)
      (ZpoleRepSeries M) Filter.atTop (Metric.closedBall x r') :=
    tendstoUniformlyOn_of_tlu_isCompact
      (repZpole_luc M D
        ⟨Metric.closedBall x r', isCompact_closedBall _ _, hballΩ, hKavoid⟩)
      (isCompact_closedBall _ _)
  have h1 : TendstoLocallyUniformlyOn
      (fun n s => repZeroPolePartial M n s)
      (ZpoleRepSeries M) Filter.atTop (Metric.ball x r') :=
    hUnif.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have h2 : DifferentiableOn ℂ (ZpoleRepSeries M) (Metric.ball x r') :=
    h1.differentiableOn
      (Filter.Eventually.of_forall (fun n =>
        (repPartial_differentiableOn M n x r hiso).mono
          (Metric.ball_subset_ball hr'lt.le)))
      Metric.isOpen_ball
  exact (h2.analyticOnNhd Metric.isOpen_ball) x (Metric.mem_ball_self hr'pos)

#print axioms repPartial_differentiableOn
#print axioms repZpole_analyticAt_nonpole

end
end RHFormalization
