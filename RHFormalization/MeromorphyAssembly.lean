import RHFormalization.MeromorphyAwayFromPoles

/-!
# RHFormalization.MeromorphyAssembly

The meromorphy campaign's goal: `MeromorphicOn Zpole Ω` is a THEOREM, from the
convergence API alone. At non-pole points: analyticity via the uniform-limit
machinery on a pole-free ball (M2B). At pole points inside Ω: the zero is
forcibly OFF-CRITICAL (re(polePoint) < 0 always, so Ω-membership forces
im ≠ 0 — M3 vacuity), and M1 fires.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- M2B helper: the full partial sums are differentiable on a pole-free ball. -/
theorem fullPartial_differentiableOn
    (M : ZeroMultiplicityData) (n : ℕ) (x : ℂ) (r : ℝ)
    (hiso : ∀ ρ : ℂ, IsNontrivialZetaZero ρ → r ≤ dist (polePoint ρ) x) :
    DifferentiableOn ℂ
      (fun s => zeroPolePartial M defaultZeroExhaustion n s)
      (Metric.ball x r) := by
  unfold zeroPolePartial finiteZeroPoleSeries
  have hterm : ∀ ρ' ∈ defaultZeroExhaustion.zeroSet n,
      DifferentiableOn ℂ (fun s => zeroPoleSummand M ρ' s)
        (Metric.ball x r) := by
    intro ρ' hρ'
    have hz' := defaultZeroExhaustion.h_all_zeros n ρ' hρ'
    intro s hs
    have hden : zeroPoleDenom ρ' s ≠ 0 := by
      have hd : zeroPoleDenom ρ' s = s - polePoint ρ' := by
        unfold zeroPoleDenom polePoint; ring
      rw [hd, sub_ne_zero]
      intro hcontra
      have hdist := hiso ρ' hz'
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
      | fun_prop (disch := assumption)
  first
    | exact DifferentiableOn.sum hterm
    | exact DifferentiableOn.fun_sum hterm

/-- M2B: Zpole is analytic at every non-pole point of Ω. -/
theorem zpole_analyticAt_nonpole
    (M : ZeroMultiplicityData) (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (x : ℂ) (hxΩ : x ∈ Ω) (hx : x ∉ ZeroPoleSet) :
    AnalyticAt ℂ Zpole x := by
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
      (fun n s => zeroPolePartial M defaultZeroExhaustion n s)
      Zpole Filter.atTop (Metric.closedBall x r') :=
    tendstoUniformlyOn_of_tlu_isCompact
      (conv.h_luc
        ⟨Metric.closedBall x r', isCompact_closedBall _ _, hballΩ, hKavoid⟩)
      (isCompact_closedBall _ _)
  have h1 : TendstoLocallyUniformlyOn
      (fun n s => zeroPolePartial M defaultZeroExhaustion n s)
      Zpole Filter.atTop (Metric.ball x r') :=
    hUnif.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have h2 : DifferentiableOn ℂ Zpole (Metric.ball x r') :=
    h1.differentiableOn
      (Filter.Eventually.of_forall (fun n =>
        (fullPartial_differentiableOn M n x r hiso).mono
          (Metric.ball_subset_ball hr'lt.le)))
      Metric.isOpen_ball
  exact (h2.analyticOnNhd Metric.isOpen_ball) x (Metric.mem_ball_self hr'pos)

/-- M3 vacuity: a pole point inside Ω comes from an OFF-CRITICAL zero. -/
theorem offCritical_of_polePoint_mem_Omega
    (ρ : ℂ) (hρ : IsNontrivialZetaZero ρ) (hΩ : polePoint ρ ∈ Ω) :
    IsOffCritical ρ := by
  obtain ⟨_, h0, h1⟩ := hρ
  intro hcrit
  apply hΩ
  constructor
  · have him : (polePoint ρ).im = ρ.im * (2 * ρ.re - 1) := by
      unfold polePoint
      simp [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [him, hcrit]
    ring
  · have hre : (polePoint ρ).re = -(ρ.re * (1 - ρ.re) + ρ.im ^ 2) := by
      unfold polePoint
      simp [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [hre]
    nlinarith

/-- THE MEROMORPHY CAMPAIGN GOAL: MeromorphicOn Zpole Ω is a theorem. -/
theorem meromorphicOn_from_convergence
    (M : ZeroMultiplicityData) (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole) :
    MeromorphicOnC Zpole Ω := by
  intro x hxΩ
  by_cases hx : x ∈ ZeroPoleSet
  · obtain ⟨ρ, hρ, hps⟩ := hx
    have hΩρ : polePoint ρ ∈ Ω := hps ▸ hxΩ
    have hoff : IsOffCritical ρ := offCritical_of_polePoint_mem_Omega ρ hρ hΩρ
    exact hps ▸ meromorphicAt_offcritical_pole M Zpole conv
      ⟨ρ, hρ, hoff, polePoint ρ, rfl, hΩρ⟩
  · exact (zpole_analyticAt_nonpole M Zpole conv x hxΩ hx).meromorphicAt

#print axioms fullPartial_differentiableOn
#print axioms zpole_analyticAt_nonpole
#print axioms offCritical_of_polePoint_mem_Omega
#print axioms meromorphicOn_from_convergence

end

end RHFormalization
