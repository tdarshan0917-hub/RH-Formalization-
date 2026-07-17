import RHFormalization.SphereUniformConvergence

/-!
# RHFormalization.HPPCauchyUpgrade

Installment 4: the maximum-principle upgrade. The shifted remainders
`Rem n s = zeroPolePartial (n+N) s − pairCoeff/(s−s0)` are uniformly Cauchy on
a closed ball around the witness pole point — differences of remainders equal
differences of partials (singular parts cancel), the sphere convergence gives
the frontier bound, and the maximum principle propagates it inward — hence
converge uniformly on the closed ball to a limit function `h`.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

theorem remainder_uniform_limit
    (M : ZeroMultiplicityData) (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (W : ZeroWitness) :
    ∃ (N : ℕ) (r2 r' : ℝ) (h : ℂ → ℂ), 0 < r' ∧ r' < r2 ∧
      Metric.closedBall W.s0 r2 ⊆ Ω ∧
      (∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
        r2 ≤ dist (polePoint ρ') W.s0) ∧
      (∀ n : ℕ, DifferentiableOn ℂ
        (fun s => zeroPolePartial M defaultZeroExhaustion (n + N) s -
          groupedResidueCoeff M (pairGroupedPoleClass M W) / (s - W.s0))
        (Metric.ball W.s0 r2)) ∧
      TendstoUniformlyOn
        (fun n s => zeroPolePartial M defaultZeroExhaustion (n + N) s -
          groupedResidueCoeff M (pairGroupedPoleClass M W) / (s - W.s0))
        h Filter.atTop (Metric.closedBall W.s0 r') := by
  obtain ⟨N, hN⟩ := pair_eventually_in W
  obtain ⟨r, hr, hiso⟩ := pairPole_isolated W
  obtain ⟨ε, hε, hball⟩ :
      ∃ ε > 0, Metric.closedBall W.s0 ε ⊆ Ω :=
    (Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_Omega_proved.mem_nhds W.hs0_in_Omega)).imp (fun ε h => ⟨h.1, h.2⟩)
  set r2 : ℝ := min r ε with hr2def
  set r' : ℝ := r2 / 2 with hr'def
  have hr2pos : 0 < r2 := lt_min hr hε
  have hr'pos : 0 < r' := by positivity
  have hr'lt : r' < r2 := by
    rw [hr'def]; linarith
  have hballΩ : Metric.closedBall W.s0 r2 ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hball
  have hiso2 : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' →
      ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ → r2 ≤ dist (polePoint ρ') W.s0 :=
    fun ρ' h1 h2 h3 => (min_le_left _ _).trans (hiso ρ' h1 h2 h3)
  set coeff : ℂ := groupedResidueCoeff M (pairGroupedPoleClass M W) with hcoeff
  set Rem : ℕ → ℂ → ℂ :=
    fun n s => zeroPolePartial M defaultZeroExhaustion (n + N) s -
      coeff / (s - W.s0) with hRem
  -- each remainder equals the finite series over the non-pair zeros
  have hRemEq : ∀ n : ℕ, Rem n = fun s =>
      finiteZeroPoleSeries M
        (defaultZeroExhaustion.zeroSet (n + N) \ pairFinset W) s := by
    intro n
    funext s
    have hst := zeroPolePartial_stabilized M W (n + N)
      (hN (n + N) (by omega)).1 (hN (n + N) (by omega)).2 s
    rw [hRem]
    simp only []
    rw [hst]
    ring
  have hRemDiff : ∀ n : ℕ, DifferentiableOn ℂ (Rem n)
      (Metric.ball W.s0 r2) := by
    intro n
    rw [hRemEq n]
    exact remainder_differentiableOn M W (n + N) r2 hr2pos hiso2
  -- sphere uniform convergence of the partials at radius r'
  have hKavoid : ∀ s ∈ Metric.sphere W.s0 r', s ∉ ZeroPoleSet := by
    intro s hs hmem
    obtain ⟨ρ', hρ', hps⟩ := hmem
    rw [Metric.mem_sphere] at hs
    by_cases hpair : ρ' = W.ρ ∨ ρ' = 1 - W.ρ
    · have hps0 : polePoint ρ' = W.s0 := by
        rcases hpair with h | h
        · rw [h]; exact W.hs0_def.symm
        · rw [h]
          have hrefl : polePoint (1 - W.ρ) = polePoint W.ρ := by
            unfold polePoint; ring
          rw [hrefl]; exact W.hs0_def.symm
      rw [hps, hps0, dist_self] at hs
      linarith
    · push_neg at hpair
      have hd := hiso2 ρ' hρ' hpair.1 hpair.2
      rw [hps] at hs
      linarith
  have hUnif : TendstoUniformlyOn
      (fun n s => zeroPolePartial M defaultZeroExhaustion n s)
      Zpole Filter.atTop (Metric.sphere W.s0 r') :=
    tendstoUniformlyOn_of_tlu_isCompact
      (conv.h_luc
        ⟨Metric.sphere W.s0 r', isCompact_sphere _ _,
          (Metric.sphere_subset_closedBall.trans
            (Metric.closedBall_subset_closedBall hr'lt.le)).trans hballΩ,
          hKavoid⟩)
      (isCompact_sphere _ _)
  -- shifted partials are uniformly Cauchy on the sphere
  have hCauchySphere := hUnif.uniformCauchySeqOn
  rw [uniformCauchySeqOn_iff] at hCauchySphere
  -- remainders are uniformly Cauchy on the CLOSED BALL (maximum principle)
  have hRC : UniformCauchySeqOn Rem Filter.atTop
      (Metric.closedBall W.s0 r') := by
    rw [uniformCauchySeqOn_iff]
    intro δ hδ
    obtain ⟨N0, hN0⟩ := hCauchySphere (δ / 2) (by linarith)
    refine ⟨N0, fun m hm n hn x hx => ?_⟩
    have hdiff : DiffContOnCl ℂ (fun z => Rem m z - Rem n z)
        (Metric.ball W.s0 r') := by
      refine DifferentiableOn.diffContOnCl ?_
      refine (((hRemDiff m).sub (hRemDiff n)).mono ?_)
      refine (closure_ball W.s0 (ne_of_gt hr'pos)).le.trans ?_
      exact Metric.closedBall_subset_ball hr'lt
    have hfront : ∀ z ∈ frontier (Metric.ball W.s0 r'),
        ‖Rem m z - Rem n z‖ ≤ δ / 2 := by
      intro z hz
      rw [frontier_ball W.s0 (ne_of_gt hr'pos)] at hz
      have h1 := hN0 (m + N) (by omega) (n + N) (by omega) z hz
      rw [dist_eq_norm] at h1
      have : Rem m z - Rem n z =
          zeroPolePartial M defaultZeroExhaustion (m + N) z -
          zeroPolePartial M defaultZeroExhaustion (n + N) z := by
        rw [hRem]; ring
      rw [this]
      linarith
    have hclos : x ∈ closure (Metric.ball W.s0 r') := by
      rw [closure_ball W.s0 (ne_of_gt hr'pos)]
      exact hx
    have := norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiff hfront hclos
    rw [dist_eq_norm]
    linarith
  -- pointwise limits + uniform upgrade
  have hlim : ∀ x ∈ Metric.closedBall W.s0 r',
      ∃ L : ℂ, Tendsto (fun n => Rem n x) Filter.atTop (nhds L) :=
    fun x hx => cauchySeq_tendsto_of_complete (hRC.cauchySeq hx)
  choose! L hL using hlim
  exact ⟨N, r2, r', L, hr'pos, hr'lt, hballΩ, hiso2, hRemDiff,
    hRC.tendstoUniformlyOn_of_tendsto hL⟩

#print axioms remainder_uniform_limit

end

end RHFormalization
