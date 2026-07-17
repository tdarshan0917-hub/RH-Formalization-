import RHFormalization.HPPStabilization

/-!
# RHFormalization.SphereUniformConvergence

Installment 3: Ω is open; locally uniform convergence on a compact set is
uniform; the sphere around a witness pole point at small radius is a legal
CompactAwayFromZeroPoles, on which the convergence API yields uniform
convergence of the partial pole series.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- Ω (the slit plane) is open: the complement of a closed set. -/
theorem isOpen_Omega_proved : IsOpen Ω := by
  have h : Ω = {s : ℂ | s.im = 0 ∧ s.re ≤ 0}ᶜ := by
    first
      | rfl
      | (ext s; rfl)
      | (ext s; exact Iff.rfl)
  rw [h]
  exact ((isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le Complex.continuous_re continuous_const)).isOpen_compl

/-- Locally uniform convergence on a compact set is uniform. -/
theorem tendstoUniformlyOn_of_tlu_isCompact
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f Filter.atTop s)
    (hs : IsCompact s) :
    TendstoUniformlyOn F f Filter.atTop s := by
  intro u hu
  choose t h1 h2 using h u hu
  have hU : ∀ (x : ℂ) (hx : x ∈ s), ∃ U : Set ℂ,
      IsOpen U ∧ x ∈ U ∧ s ∩ U ⊆ t x hx := by
    intro x hx
    obtain ⟨U, hUo, hxU, hUsub⟩ := mem_nhdsWithin.mp (h1 x hx)
    exact ⟨U, hUo, hxU, fun y hy => hUsub ⟨hy.2, hy.1⟩⟩
  choose U hUo hxU hUsub using hU
  obtain ⟨ι, hι⟩ := hs.elim_nhds_subcover' (fun x hx => U x hx)
    (fun x hx => (hUo x hx).mem_nhds (hxU x hx))
  have hev : ∀ᶠ n in Filter.atTop, ∀ x ∈ ι,
      ∀ y ∈ t x.1 x.2, (f y, F n y) ∈ u := by
    rw [Filter.eventually_all_finset]
    intro x _
    exact h2 x.1 x.2
  filter_upwards [hev] with n hn y hy
  obtain ⟨x, hxι, hyU⟩ := Set.mem_iUnion₂.mp (hι hy)
  exact hn x hxι y (hUsub x.1 x.2 ⟨hy, hyU⟩)

/-- Installment-3 main theorem. -/
theorem sphere_uniform_from_API
    (M : ZeroMultiplicityData) (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (W : ZeroWitness) :
    ∃ r' : ℝ, 0 < r' ∧
      Metric.closedBall W.s0 r' ⊆ Ω ∧
      (∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
        r' < dist (polePoint ρ') W.s0) ∧
      TendstoUniformlyOn
        (fun n s => zeroPolePartial M defaultZeroExhaustion n s)
        Zpole Filter.atTop (Metric.sphere W.s0 r') := by
  obtain ⟨r, hr, hiso⟩ := pairPole_isolated W
  obtain ⟨ε, hε, hball⟩ :
      ∃ ε > 0, Metric.closedBall W.s0 ε ⊆ Ω :=
    (Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_Omega_proved.mem_nhds W.hs0_in_Omega)).imp (fun ε h => ⟨h.1, h.2⟩)
  set r' : ℝ := min (r / 2) ε with hr'def
  have hr'pos : 0 < r' := lt_min (by linarith) hε
  have hr'lt : r' < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr'le : r' ≤ ε := min_le_right _ _
  have hballΩ : Metric.closedBall W.s0 r' ⊆ Ω :=
    (Metric.closedBall_subset_closedBall hr'le).trans hball
  have hisoStrict : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' →
      ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ → r' < dist (polePoint ρ') W.s0 :=
    fun ρ' h1 h2 h3 => lt_of_lt_of_le hr'lt (hiso ρ' h1 h2 h3)
  have hK : ∀ s ∈ Metric.sphere W.s0 r', s ∉ ZeroPoleSet := by
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
      have hd := hisoStrict ρ' hρ' hpair.1 hpair.2
      rw [hps] at hs
      linarith
  refine ⟨r', hr'pos, hballΩ, hisoStrict, ?_⟩
  exact tendstoUniformlyOn_of_tlu_isCompact
    (conv.h_luc
      ⟨Metric.sphere W.s0 r', isCompact_sphere _ _,
        Metric.sphere_subset_closedBall.trans hballΩ, hK⟩)
    (isCompact_sphere _ _)

#print axioms isOpen_Omega_proved
#print axioms tendstoUniformlyOn_of_tlu_isCompact
#print axioms sphere_uniform_from_API

end

end RHFormalization
