import RHFormalization.OmegaTopology
import RHFormalization.PerturbedResidual
import Mathlib

/-!
# Ball → compact lift for the prime residual bound (hLB structural step)

Lifts the BANKED closed-ball residual bound to bounded on every COMPACT K ⊆ Ω
via finite subcover + finite max. Pure topology.
-/

namespace RHFormalization
open Complex Set Metric

theorem perturbedResidual_bound_on_compact_of_ball_bounds
    {N : ℕ} (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (B : ℂ → ℂ)
    (ball_bound :
      ∀ c : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ Ω →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Metric.closedBall c r,
          ‖perturbedResidual μ hV B s‖ ≤ C)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖perturbedResidual μ hV B s‖ ≤ C := by
  classical
  have hΩopen : IsOpen Ω := isOpen_Omega_native
  -- total radius r and total bound Cf, junk outside K
  have hpt : ∀ x : ℂ, ∃ rx : ℝ, 0 < rx ∧ (x ∈ K → Metric.closedBall x rx ⊆ Ω) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨r0, hr0, hsub⟩ := Metric.isOpen_iff.mp hΩopen x (hKΩ hx)
      exact ⟨r0/2, by positivity,
        fun _ => subset_trans (Metric.closedBall_subset_ball (by linarith)) hsub⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hrpos hrsub using hpt
  have hCtot : ∀ x : ℂ, ∃ C : ℝ, 0 ≤ C ∧
      (x ∈ K → ∀ s ∈ Metric.closedBall x (r x), ‖perturbedResidual μ hV B s‖ ≤ C) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨C, hC0, hCbd⟩ := ball_bound x (r x) (hrpos x) (hrsub x hx)
      exact ⟨C, hC0, fun _ => hCbd⟩
    · exact ⟨0, le_refl 0, fun h => absurd h hx⟩
  choose Cf hCf0 hCfbd using hCtot
  -- finite subcover: use the Finset-valued elim_finite_subcover
  have hcover : K ⊆ ⋃ (x : ℂ) (_ : x ∈ K), Metric.ball x (r x) := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨y, hy, Metric.mem_ball_self (hrpos y)⟩
  -- reindex over the subtype to get a Finset subcover
  have hcover' : K ⊆ ⋃ (p : K), Metric.ball (p : ℂ) (r p) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hrpos y)⟩
  obtain ⟨t, htcover⟩ :=
    hK.elim_finite_subcover (fun p : K => Metric.ball (p : ℂ) (r p))
      (fun _ => Metric.isOpen_ball) hcover'
  rcases t.eq_empty_or_nonempty with htempty | htne
  · refine ⟨0, le_refl 0, ?_⟩
    intro s hs
    exfalso
    obtain ⟨p, hp, _⟩ := Set.mem_iUnion₂.mp (htcover hs)
    rw [htempty] at hp
    exact absurd hp (Finset.notMem_empty p)
  · refine ⟨t.sup' htne (fun p => Cf (p : ℂ)), ?_, ?_⟩
    · obtain ⟨p, hp⟩ := htne
      have := Finset.le_sup' (s := t) (fun p => Cf (p : ℂ)) hp
      exact le_trans (hCf0 (p : ℂ)) this
    · intro s hs
      obtain ⟨p, hp, hsp⟩ := Set.mem_iUnion₂.mp (htcover hs)
      have hsclosed : s ∈ Metric.closedBall (p : ℂ) (r p) :=
        Metric.ball_subset_closedBall hsp
      have hle := Finset.le_sup' (s := t) (fun p => Cf (p : ℂ)) hp
      exact le_trans (hCfbd (p : ℂ) p.2 s hsclosed) hle

#print axioms perturbedResidual_bound_on_compact_of_ball_bounds

end RHFormalization
