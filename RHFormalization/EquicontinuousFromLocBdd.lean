import RHFormalization.MontelEquicontinuousOn
import RHFormalization.AscoliBridgeLayer3
import RHFormalization.MontelUniqueLimit
import RHFormalization.AscoliRelativelyCompactBoxed
import RHFormalization.AscoliObligationDirect
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Filter Topology Complex Metric Set

/-- EquicontinuousOn Omega of the ℂ-family, from h_holo + h_loc_bdd, via the green ball lemma. -/
theorem equicontinuousOn_Omega_of_holo_loc_bdd
    (F : ℕ → ℂ → ℂ)
    (h_holo : ∀ n, HolomorphicOnC (F n) Ω)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) :
    EquicontinuousOn (fun n => F n) Ω := by
  have hdiff : ∀ n, DifferentiableOn ℂ (F n) Ω := fun n => (h_holo n).differentiableOn
  intro z0 hz0
  obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp isOpen_Omega z0 hz0
  set ρ : ℝ := r/4 with hρ
  set rr : ℝ := r/4 with hrr
  have hrr0 : 0 < rr := by rw [hrr]; linarith
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hballsub : closedBall z0 (ρ + rr) ⊆ Ω := by
    have hhalf : ρ + rr = r/2 := by rw [hρ, hrr]; ring
    rw [hhalf]
    intro w hw
    apply hrsub
    rw [Metric.mem_ball]
    have hd : dist w z0 ≤ r/2 := by rwa [Metric.mem_closedBall] at hw
    linarith
  have hKcompact : IsCompact (closedBall z0 (ρ + rr)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := h_loc_bdd (closedBall z0 (ρ + rr)) hKcompact hballsub
  set M : ℝ := |C| + 1 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hbd : ∀ n, ∀ w ∈ closedBall z0 (ρ + rr), ‖F n w‖ ≤ M := by
    intro n w hw
    rw [hM]
    calc ‖F n w‖ ≤ C := hC n w hw
      _ ≤ |C| := le_abs_self _
      _ ≤ |C| + 1 := by linarith
  have hunif : UniformEquicontinuousOn (fun n => F n) (ball z0 ρ) :=
    uniformEquicontinuousOn_ball_of_bounded_holo (fun n => F n) isOpen_Omega hrr0 hM0
      hballsub hdiff hbd
  have heqOn_ball : EquicontinuousOn (fun n => F n) (ball z0 ρ) := hunif.equicontinuousOn
  have hz0ball : z0 ∈ ball z0 ρ := by rw [Metric.mem_ball, dist_self]; exact hρ0
  have hballOmega : ball z0 ρ ⊆ Ω := by
    intro w hw
    apply hrsub
    rw [Metric.mem_ball] at hw ⊢
    rw [hρ] at hw; linarith
  have hwithin_ball : EquicontinuousWithinAt (fun n => F n) (ball z0 ρ) z0 :=
    heqOn_ball z0 hz0ball
  -- transfer within-ball to within-Omega: ball open ∋ z0, so 𝓝[Ω] z0 = 𝓝[Ω ∩ ball] z0,
  -- and Ω ∩ ball = ball (ball ⊆ Ω), so the eventually transfers.
  intro U hU
  have hev := hwithin_ball U hU
  rw [nhdsWithin_restrict _ hz0ball (isOpen_ball)]
  have hinter : Ω ∩ ball z0 ρ = ball z0 ρ := Set.inter_eq_right.mpr hballOmega
  rw [hinter]
  exact hev

#print axioms equicontinuousOn_Omega_of_holo_loc_bdd

/-- Bundled equicontinuity: the C(Ω,ℂ) family from F is equicontinuous, via restrict_iff. -/
theorem equicontinuous_bundled_of_holo_loc_bdd
    (F : ℕ → ℂ → ℂ)
    (h_holo : ∀ n, HolomorphicOnC (F n) Ω)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) :
    Equicontinuous (fun n => ((bundleC (F n) (h_holo n)) : (Ω : Set ℂ) → ℂ)) := by
  -- (↑(bundleC (F n) _)) = Ω.restrict (F n), so the family = Ω.restrict ∘ F
  have hfun : (fun n => ((bundleC (F n) (h_holo n)) : (Ω : Set ℂ) → ℂ))
      = (Ω : Set ℂ).restrict ∘ F := by
    funext n x
    rfl
  rw [hfun]
  rw [equicontinuous_restrict_iff]
  exact equicontinuousOn_Omega_of_holo_loc_bdd F h_holo h_loc_bdd

#print axioms equicontinuous_bundled_of_holo_loc_bdd

/-- **THE BRICK.** AscoliExtractionHyp from h_stage_holo + h_loc_bdd, NO equicontinuity hypothesis
(proven internally). Drops hRC from realLayerDMaster_montel. -/
theorem ascoliExtractionHyp_of_holo_loc_bdd
    (F : ℕ → ℂ → ℂ)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) :
    AscoliExtractionHyp F := by
  intro h_holo
  -- pointwise bound M from h_loc_bdd on singletons
  classical
  let M : (Ω : Set ℂ) → ℝ := fun x =>
    |Classical.choose (h_loc_bdd ({(x : ℂ)} : Set ℂ) isCompact_singleton
      (by intro z hz; simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact x.property))| + 1
  apply ascoliRelativelyCompact_of_obligation ascoliRelCompactObligation_direct
    (G := fun n => bundleC (F n) (h_holo n)) (M := M)
  · -- pointwise bound: bundleC (F n) at x ∈ closedBall 0 (M x)
    intro x n
    have hspec := Classical.choose_spec (h_loc_bdd ({(x : ℂ)} : Set ℂ) isCompact_singleton
      (by intro z hz; simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact x.property))
    have hx : (x : ℂ) ∈ ({(x : ℂ)} : Set ℂ) := rfl
    have hb : ‖F n (x : ℂ)‖ ≤ Classical.choose (h_loc_bdd ({(x : ℂ)} : Set ℂ) isCompact_singleton
      (by intro z hz; simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact x.property)) :=
      hspec n (x : ℂ) hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hval : (bundleC (F n) (h_holo n)) x = F n (x : ℂ) := rfl
    rw [hval]
    calc ‖F n (x : ℂ)‖ ≤ _ := hb
      _ ≤ |_| := le_abs_self _
      _ ≤ M x := by dsimp only [M]; linarith
  · -- equicontinuity: reindex the green ℕ-family over the range of bundled maps (Equicontinuous.comp)
    classical
    set Gc : ℕ → C((Ω : Set ℂ), ℂ) := fun n => bundleC (F n) (h_holo n) with hGc
    -- pick an ℕ-index for each range element
    let pick : Set.range Gc → ℕ := fun x => Classical.choose x.property
    have hpick : ∀ x : Set.range Gc, Gc (pick x) = (x : C((Ω : Set ℂ), ℂ)) :=
      fun x => Classical.choose_spec x.property
    -- green ℕ-indexed equicontinuity
    have hN : Equicontinuous (fun n : ℕ => ((Gc n) : (Ω : Set ℂ) → ℂ)) := by
      simpa [hGc] using equicontinuous_bundled_of_holo_loc_bdd F h_holo h_loc_bdd
    -- reindex by pick
    have hpick_equi : Equicontinuous
        (fun x : Set.range Gc => ((Gc (pick x)) : (Ω : Set ℂ) → ℂ)) := by
      simpa [Function.comp_def] using hN.comp pick
    -- the picked representative equals the range element
    have hfamily :
        (fun x : Set.range Gc => ((x : C((Ω : Set ℂ), ℂ)) : (Ω : Set ℂ) → ℂ))
          = (fun x : Set.range Gc => ((Gc (pick x)) : (Ω : Set ℂ) → ℂ)) := by
      funext x
      rw [hpick x]
    rw [hfamily]
    exact hpick_equi

#print axioms ascoliExtractionHyp_of_holo_loc_bdd

end
end RHFormalization
