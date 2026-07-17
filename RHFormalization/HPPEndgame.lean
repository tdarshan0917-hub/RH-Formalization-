import RHFormalization.HPPCauchyUpgrade

/-!
# RHFormalization.HPPEndgame

Installment 5 — the campaign's goal theorem. From the locally uniform
convergence API alone, every off-critical zero witness receives its principal
part with the honest reflection-pair coefficient. `h_pp` is hereby DERIVED,
not assumed.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

theorem h_pp_from_convergence
    (M : ZeroMultiplicityData) (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (W : ZeroWitness) :
    HasPrincipalPartAtC Zpole W.s0
      (groupedResidueCoeff M (pairGroupedPoleClass M W)) := by
  obtain ⟨N, r2, r', h, hr'pos, hr'lt, hballΩ, hiso2, hRemDiff, hUnif⟩ :=
    remainder_uniform_limit M Zpole conv W
  set coeff : ℂ := groupedResidueCoeff M (pairGroupedPoleClass M W) with hco
  -- (i) the limit is analytic at the pole point
  have hAnalytic : AnalyticAt ℂ h W.s0 := by
    have h1 : TendstoLocallyUniformlyOn
        (fun n s => zeroPolePartial M defaultZeroExhaustion (n + N) s -
          coeff / (s - W.s0))
        h Filter.atTop (Metric.ball W.s0 r') :=
      hUnif.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
    have h2 : DifferentiableOn ℂ h (Metric.ball W.s0 r') :=
      h1.differentiableOn
        (Filter.Eventually.of_forall (fun n =>
          (hRemDiff n).mono (Metric.ball_subset_ball hr'lt.le)))
        Metric.isOpen_ball
    exact (h2.analyticOnNhd Metric.isOpen_ball) W.s0 (Metric.mem_ball_self hr'pos)
  refine ⟨h, hAnalytic, ?_⟩
  -- (ii)+(iii): the eventual identity off the center
  filter_upwards [Metric.ball_mem_nhds W.s0 hr'pos] with w hw hne
  have hdist : dist w W.s0 < r' := Metric.mem_ball.mp hw
  -- remainders converge pointwise to h w
  have hRw : Tendsto
      (fun n => zeroPolePartial M defaultZeroExhaustion (n + N) w -
        coeff / (w - W.s0))
      Filter.atTop (nhds (h w)) :=
    hUnif.tendsto_at (Metric.ball_subset_closedBall hw)
  -- w avoids the pole set, so the partials converge pointwise to Zpole w
  have hwΩ : w ∈ Ω := by
    refine hballΩ ?_
    rw [Metric.mem_closedBall]
    linarith
  have hwAvoid : ∀ s ∈ ({w} : Set ℂ), s ∉ ZeroPoleSet := by
    intro s hs hmem
    rw [Set.mem_singleton_iff] at hs
    subst hs
    obtain ⟨ρ', hρ', hps⟩ := hmem
    by_cases hpair : ρ' = W.ρ ∨ ρ' = 1 - W.ρ
    · have hps0 : polePoint ρ' = W.s0 := by
        rcases hpair with hp | hp
        · rw [hp]; exact W.hs0_def.symm
        · rw [hp]
          have hrefl : polePoint (1 - W.ρ) = polePoint W.ρ := by
            unfold polePoint; ring
          rw [hrefl]; exact W.hs0_def.symm
      rw [hps0] at hps
      exact hne hps
    · push_neg at hpair
      have hd := hiso2 ρ' hρ' hpair.1 hpair.2
      rw [hps] at hdist
      linarith [hd, hdist]
  have hpart : Tendsto
      (fun n => zeroPolePartial M defaultZeroExhaustion n w)
      Filter.atTop (nhds (Zpole w)) := by
    have htlu := conv.h_luc
      ⟨{w}, isCompact_singleton, Set.singleton_subset_iff.mpr hwΩ, hwAvoid⟩
    exact htlu.tendsto_at (Set.mem_singleton w)
  have hpartShift : Tendsto
      (fun n => zeroPolePartial M defaultZeroExhaustion (n + N) w)
      Filter.atTop (nhds (Zpole w)) :=
    (tendsto_add_atTop_iff_nat N).mpr hpart
  have hRw2 : Tendsto
      (fun n => zeroPolePartial M defaultZeroExhaustion (n + N) w -
        coeff / (w - W.s0))
      Filter.atTop (nhds (Zpole w - coeff / (w - W.s0))) :=
    hpartShift.sub_const _
  have hkey : h w = Zpole w - coeff / (w - W.s0) :=
    tendsto_nhds_unique hRw hRw2
  first
    | linear_combination -hkey
    | linear_combination hkey
    | (rw [hkey]; ring)

#print axioms h_pp_from_convergence

end

end RHFormalization
