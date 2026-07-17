import RHFormalization.AscoliObligationDirect
import RHFormalization.AscoliRelativelyCompactBoxed
import RHFormalization.AscoliBridgeLayer3
import RHFormalization.MontelEquicontinuousOn
import RHFormalization.AdmissibleBMontelWiring

/-!
# The loc-bdd → Ascoli bridge, CLEAN (replaces the sorried draft)

`ascoliExtractionHyp_of_loc_bdd`: local boundedness of a holomorphic family
gives the bundled Ascoli hypothesis — pointwise bounds from singleton
compacts, equicontinuity from the banked Lipschitz-on-ball Cauchy estimate,
relative compactness from the banked DIRECT obligation.

Endpoint: `RH_from_admissible_B_locbdd` — RH from exactly TWO inputs:
the continued overlap object `Bω` (App H pole package) and the S(t,R)
local-boundedness anchor for the admissible B-stages.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Metric Set

open scoped NNReal

/-- ε-δ equicontinuity seed at a point of Ω, from local boundedness via the
banked Lipschitz-on-ball lemma. -/
theorem dist_lt_of_locbdd_holo
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, HolomorphicOnC (F n) Ω)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C)
    (x₀ : ℂ) (hx₀ : x₀ ∈ Ω) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℂ, dist y x₀ < δ → ∀ n : ℕ,
        dist (F n x₀) (F n y) < ε := by
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_Omega x₀ hx₀
  have hr4 : (0 : ℝ) < r / 4 := by linarith
  have hsub : Metric.closedBall x₀ (r / 4 + r / 4) ⊆ Ω := by
    refine Set.Subset.trans ?_ hball
    apply Metric.closedBall_subset_ball
    linarith
  obtain ⟨C, hC⟩ := h_loc_bdd (Metric.closedBall x₀ (r / 4 + r / 4))
    (isCompact_closedBall _ _) hsub
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hbd : ∀ n : ℕ, ∀ w ∈ Metric.closedBall x₀ (r / 4 + r / 4),
      ‖F n w‖ ≤ max C 0 :=
    fun n w hw => le_trans (hC n w hw) (le_max_left _ _)
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) Ω := by
    intro n
    first
      | exact ((isOpen_Omega.analyticOn_iff_analyticOnNhd).mp
          (hF n)).differentiableOn
      | exact (hF n).differentiableOn
  have hlip := lipschitzOnWith_ball_of_bounded_holo F isOpen_Omega
    hr4 hM0 hsub hdiff hbd
  obtain ⟨K0, hlip'⟩ : ∃ K : ℝ≥0, ∀ n : ℕ,
      LipschitzOnWith K (F n) (Metric.ball x₀ (r / 4)) := ⟨_, hlip⟩
  have hK0 : (0 : ℝ) ≤ (K0 : ℝ) := by
    first
      | exact K0.coe_nonneg
      | exact NNReal.coe_nonneg K0
      | positivity
  have h1 : (0 : ℝ) < (K0 : ℝ) + 1 := by linarith
  have hApos : (0 : ℝ) < ε / ((K0 : ℝ) + 1) := div_pos hε h1
  refine ⟨min (ε / ((K0 : ℝ) + 1)) (r / 8), lt_min hApos (by linarith), ?_⟩
  intro y hy n
  have hyball : y ∈ Metric.ball x₀ (r / 4) := by
    rw [Metric.mem_ball]
    have h2 : dist y x₀ < r / 8 :=
      lt_of_lt_of_le hy (min_le_right _ _)
    linarith
  have hxball : x₀ ∈ Metric.ball x₀ (r / 4) := Metric.mem_ball_self hr4
  have hd := (hlip' n).dist_le_mul x₀ hxball y hyball
  have hA : (K0 : ℝ) * (ε / ((K0 : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc]
    first
      | (rw [div_lt_iff h1]; nlinarith)
      | (rw [div_lt_iff₀ h1]; nlinarith)
  calc dist (F n x₀) (F n y)
      ≤ (K0 : ℝ) * dist x₀ y := hd
    _ ≤ (K0 : ℝ) * (ε / ((K0 : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        rw [dist_comm]
        exact le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
    _ < ε := hA

/-- **The bridge**: stage-holo + loc-bdd ⟹ the bundled Ascoli hypothesis. -/
theorem ascoliExtractionHyp_of_loc_bdd
    (F : ℕ → ℂ → ℂ)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) :
    AscoliExtractionHyp F := by
  intro hF
  classical
  refine ascoliRelativelyCompact_of_obligation ascoliRelCompactObligation_direct
    (fun n => bundleC (F n) (hF n))
    (fun x => Classical.choose (h_loc_bdd {(x : ℂ)} isCompact_singleton
      (Set.singleton_subset_iff.mpr x.property)))
    ?_ ?_
  · intro x n
    have hspec := Classical.choose_spec (h_loc_bdd {(x : ℂ)} isCompact_singleton
      (Set.singleton_subset_iff.mpr x.property))
    have hmem : (x : ℂ) ∈ ({(x : ℂ)} : Set ℂ) := by
      first
        | exact Set.mem_singleton _
        | rfl
        | simp
    have hb := hspec n (x : ℂ) hmem
    rw [Metric.mem_closedBall, dist_zero_right]
    first
      | exact hb
      | (show ‖F n (x : ℂ)‖ ≤ _
         exact hb)
      | simpa [bundleC_apply] using hb
  · intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hspec⟩ := dist_lt_of_locbdd_holo F hF h_loc_bdd
      (x₀ : ℂ) x₀.property ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro y hy i
    have hyd : dist ((y : ℂ)) ((x₀ : ℂ)) < δ := by
      first
        | exact hy
        | (rwa [Subtype.dist_eq] at hy)
    obtain ⟨n, hn⟩ := i.property
    have hn' : bundleC (F n) (hF n) = (i : C(Ω, ℂ)) := hn
    have h1 := hspec (y : ℂ) hyd n
    first
      | exact h1
      | (show dist (((i : C(Ω, ℂ)) : (Ω : Set ℂ) → ℂ) x₀)
            (((i : C(Ω, ℂ)) : (Ω : Set ℂ) → ℂ) y) < ε
         rw [← hn']
         exact h1)
      | (rw [← hn']
         exact h1)
      | (simpa [← hn', bundleC_apply] using h1)
      | (simpa [← hn'] using h1)

/-- **AscoliExtraction from loc-bdd alone** (composing the banked layer-3). -/
theorem ascoliExtraction_of_loc_bdd
    (F : ℕ → ℂ → ℂ)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) :
    AscoliExtraction F :=
  ascoliExtraction_of_relativelyCompact
    (ascoliExtractionHyp_of_loc_bdd F h_loc_bdd)

/-- **THE COLLAPSED ENDPOINT — RH from `(Bω, h_loc_bdd)` alone.** -/
theorem RH_from_admissible_B_locbdd
    (Bω : ℂ → ℂ) (hBω_holo : HolomorphicOnC Bω Ω)
    (hBω_overlap : ∀ s ∈ RightHalfPlane (1 : ℝ),
        Bω s = galerkinBcanLimitData.Bcan s)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖admissibleBStageFamily n s‖ ≤ C) :
    RiemannHypothesis :=
  RH_from_admissible_B_montel Bω hBω_holo hBω_overlap h_loc_bdd
    (ascoliExtraction_of_loc_bdd admissibleBStageFamily h_loc_bdd)

#print axioms dist_lt_of_locbdd_holo
#print axioms ascoliExtractionHyp_of_loc_bdd
#print axioms ascoliExtraction_of_loc_bdd
#print axioms RH_from_admissible_B_locbdd

end

end RHFormalization
