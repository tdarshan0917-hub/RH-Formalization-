import RHFormalization.ResolventTraceHolo
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# RHFormalization.BallCutDistance
Uniform `δ > 0` with `‖s+λ‖ ≥ δ` on `closedBall c r ⊆ Ω`, for all `λ ≥ 0`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric

theorem normSq_add_lam_ge (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam) :
    s.im ^ 2 ≤ ‖s + (lam : ℂ)‖ ^ 2 ∧
    (0 ≤ s.re → s.re ^ 2 + s.im ^ 2 ≤ ‖s + (lam : ℂ)‖ ^ 2) := by
  have hnsq : ‖s + (lam : ℂ)‖ ^ 2 = (s.re + lam) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine ⟨?_, ?_⟩
  · rw [hnsq]; nlinarith [sq_nonneg (s.re + lam)]
  · intro hre; rw [hnsq]; nlinarith [hlam, hre, sq_nonneg lam]

noncomputable def psiCut (s : ℂ) : ℝ := if 0 ≤ s.re then ‖s‖ else |s.im|

theorem psiCut_le_norm_add (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam) :
    psiCut s ≤ ‖s + (lam : ℂ)‖ := by
  have hnn : 0 ≤ ‖s + (lam : ℂ)‖ := norm_nonneg _
  obtain ⟨him, hre⟩ := normSq_add_lam_ge s lam hlam
  unfold psiCut
  split_ifs with h
  · have hsnorm : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hsq : ‖s‖ ^ 2 ≤ ‖s + (lam : ℂ)‖ ^ 2 := by rw [hsnorm]; exact hre h
    nlinarith [hsq, norm_nonneg s, hnn]
  · have hsq : |s.im| ^ 2 ≤ ‖s + (lam : ℂ)‖ ^ 2 := by rw [sq_abs]; exact him
    nlinarith [hsq, abs_nonneg s.im, hnn]

theorem psiCut_pos_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) : 0 < psiCut s := by
  unfold psiCut
  split_ifs with h
  · rw [norm_pos_iff]
    intro hs0
    exact hs ⟨by rw [hs0]; simp, by rw [hs0]; simp⟩
  · push_neg at h
    rw [abs_pos]
    intro him0
    exact hs ⟨him0, le_of_lt h⟩

theorem continuous_psiCut : Continuous psiCut := by
  have hnorm : Continuous (fun s : ℂ => ‖s‖) := continuous_norm
  have haim : Continuous (fun s : ℂ => |s.im|) := continuous_abs.comp Complex.continuous_im
  have hzero : Continuous (fun _ : ℂ => (0:ℝ)) := continuous_const
  have hre : Continuous (fun s : ℂ => s.re) := Complex.continuous_re
  have hagree : ∀ s : ℂ, (0:ℝ) = s.re → ‖s‖ = |s.im| := by
    intro s hs
    have hre0 : s.re = 0 := hs.symm
    have h1 : ‖s‖ ^ 2 = s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre0]; ring
    have h2 : |s.im| ^ 2 = s.im ^ 2 := sq_abs _
    nlinarith [h1, h2, norm_nonneg s, abs_nonneg s.im]
  have := Continuous.if_le hnorm haim hzero hre hagree
  simpa [psiCut] using this

theorem exists_uniform_lower_bound_on_ball
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Metric.closedBall c r, ∀ lam : ℝ, 0 ≤ lam →
      δ ≤ ‖s + (lam : ℂ)‖ := by
  have hcompact : IsCompact (Metric.closedBall c r) := isCompact_closedBall c r
  have hne : (Metric.closedBall c r).Nonempty := ⟨c, Metric.mem_closedBall_self hr.le⟩
  have hcont : ContinuousOn psiCut (Metric.closedBall c r) :=
    continuous_psiCut.continuousOn
  obtain ⟨x₀, hx₀mem, hx₀min⟩ := hcompact.exists_isMinOn hne hcont
  refine ⟨psiCut x₀, psiCut_pos_of_mem_Omega (hball hx₀mem), ?_⟩
  intro s hsmem lam hlam
  have hmin : psiCut x₀ ≤ psiCut s := hx₀min hsmem
  exact hmin.trans (psiCut_le_norm_add s lam hlam)

#print axioms continuous_psiCut
#print axioms exists_uniform_lower_bound_on_ball

/-- Ball radius bound: every s in closedBall c r has norm at most ‖c‖ + r. -/
theorem norm_le_on_closedBall {c : ℂ} {r : ℝ} {s : ℂ}
    (hs : s ∈ Metric.closedBall c r) : ‖s‖ ≤ ‖c‖ + r := by
  have h : dist s c ≤ r := Metric.mem_closedBall.mp hs
  have hd : ‖s - c‖ ≤ r := by simpa [dist_eq_norm] using h
  calc ‖s‖ = ‖(s - c) + c‖ := by ring_nf
    _ ≤ ‖s - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + r := by linarith

/-- Brick 3 (Cor. A.TRACE): on a closed ball in Omega, the resolvent terms admit a
summable majorant C * (1 + lam n)⁻¹, given eigenvalue summability. -/
theorem exists_summable_bound_on_ball
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r ⊆ Ω)
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 ≤ lam n)
    (hsum : Summable (fun n => (1 + lam n)⁻¹)) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ s ∈ Metric.ball c r, ‖(s + (lam n : ℂ))⁻¹‖ ≤ u n := by
  obtain ⟨delta, hdpos, hd⟩ := exists_uniform_lower_bound_on_ball c r hr hball
  set R : ℝ := ‖c‖ + r with hRdef
  have hRnn : 0 ≤ R := by have := norm_nonneg c; linarith
  set C : ℝ := (1 + R) / delta + 1 with hCdef
  refine ⟨fun n => C * (1 + lam n)⁻¹, hsum.mul_left C, ?_⟩
  intro n s hs
  have hsclosed : s ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hs
  have hlow : delta ≤ ‖s + (lam n : ℂ)‖ := hd s hsclosed (lam n) (hlam n)
  have hpos : 0 < ‖s + (lam n : ℂ)‖ := lt_of_lt_of_le hdpos hlow
  have hsR : ‖s‖ ≤ R := norm_le_on_closedBall hsclosed
  have hnl : ‖(lam n : ℂ)‖ = lam n := by
    rw [Complex.norm_real]; exact abs_of_nonneg (hlam n)
  have hgrow : (lam n : ℝ) - R ≤ ‖s + (lam n : ℂ)‖ := by
    have h1 : ‖(lam n : ℂ)‖ - ‖(-s)‖ ≤ ‖(lam n : ℂ) - (-s)‖ := norm_sub_norm_le _ _
    have hns : ‖(-s)‖ = ‖s‖ := norm_neg s
    have hsub : ‖(lam n : ℂ) - (-s)‖ = ‖s + (lam n : ℂ)‖ := by
      rw [sub_neg_eq_add, add_comm]
    rw [hns, hsub, hnl] at h1
    linarith
  have h1lpos : (0:ℝ) < 1 + lam n := by have := hlam n; linarith
  have hge1 : (1:ℝ) ≤ ‖s + (lam n : ℂ)‖ / delta := by
    rw [le_div_iff₀ hdpos]; linarith
  have hcore : (1 + lam n : ℝ) ≤ C * ‖s + (lam n : ℂ)‖ := by
    have hA : (1 + R : ℝ) ≤ (1 + R) / delta * ‖s + (lam n : ℂ)‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
      nlinarith [hge1, hdpos, hRnn, hpos]
    have hsum2 : (1 + lam n : ℝ) ≤ (1 + R) / delta * ‖s + (lam n : ℂ)‖ + 1 * ‖s + (lam n : ℂ)‖ := by
      have hB : (lam n : ℝ) - R ≤ 1 * ‖s + (lam n : ℂ)‖ := by rw [one_mul]; exact hgrow
      linarith
    rw [hCdef]; nlinarith [hsum2]
  rw [norm_inv, inv_le_iff_one_le_mul₀ hpos]
  have hmul : (1 + lam n : ℝ) * (1 + lam n)⁻¹ = 1 := by field_simp
  calc (1:ℝ) = (1 + lam n) * (1 + lam n)⁻¹ := by rw [hmul]
    _ ≤ (C * ‖s + (lam n : ℂ)‖) * (1 + lam n)⁻¹ := by
        apply mul_le_mul_of_nonneg_right hcore; positivity
    _ = C * (1 + lam n)⁻¹ * ‖s + (lam n : ℂ)‖ := by ring

#print axioms norm_le_on_closedBall
#print axioms exists_summable_bound_on_ball

/-- **Operator-side engine, assembled.** The resolvent-trace sum
`F_stage(s) = ∑ₙ 1/(s+λₙ)` is holomorphic on `Ω`, resting on the single honest
input `Summable (1+λₙ)⁻¹` (Lemma A.GROWTH: eigenvalue growth ⇒ summability).
No per-ball hypothesis, no trace-class theory, no zero-location input. -/
theorem Fstage_holo_from_summable
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 ≤ lam n)
    (hsum : Summable (fun n => (1 + lam n)⁻¹)) :
    HolomorphicOnC (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) Ω := by
  refine Fstage_holo_on_Omega lam hlam ?_
  intro z hz
  -- openness of Ω gives an open ball around z inside Ω
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp isOpen_Omega_native z hz
  -- halve it so the CLOSED ball of radius ε/2 sits inside Ω
  refine ⟨ε / 2, by linarith, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith)).trans hεsub
  · have hclosed : Metric.closedBall z (ε / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεsub
    obtain ⟨u, husum, hubd⟩ :=
      exists_summable_bound_on_ball z (ε / 2) (by linarith) hclosed lam hlam hsum
    exact ⟨u, husum, hubd⟩

#print axioms Fstage_holo_from_summable

end

end RHFormalization
