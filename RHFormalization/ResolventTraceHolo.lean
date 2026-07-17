import RHFormalization.AnalyticWrappers
import RHFormalization.DefaultOmegaPreperfect
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Constructions

/-!
# RHFormalization.ResolventTraceHolo

Engine bricks 2 / 2b / 2c (no holes): the resolvent-trace sum
`F_stage(s) = ∑ₙ 1/(s+λₙ)` is holomorphic on `Ω`, matching Appendix-A
Cor. A.TRACE / A.HOLO.  No trace-class operator theory.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- `s + λ ≠ 0` for `s ∈ Ω` and `λ ≥ 0`. -/
theorem add_real_ne_zero_of_mem_Omega {z : ℂ} (hz : z ∈ Ω) {lam : ℝ} (hlam : 0 ≤ lam) :
    z + (lam : ℂ) ≠ 0 := by
  intro h
  apply hz
  have hzeq : z = -(lam : ℂ) := by linear_combination h
  refine ⟨?_, ?_⟩
  · rw [hzeq]; simp
  · rw [hzeq]; simp; linarith

/-- Each resolvent term is analytic *at* any point of `Ω`. -/
theorem resolvent_term_analyticAt (lam : ℝ) (hlam : 0 ≤ lam) {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ (fun s => (s + (lam : ℂ))⁻¹) z := by
  have hbase : AnalyticAt ℂ (fun s : ℂ => s + (lam : ℂ)) z :=
    analyticAt_id.add analyticAt_const
  have hne : (fun s : ℂ => s + (lam : ℂ)) z ≠ 0 := by
    simpa using add_real_ne_zero_of_mem_Omega hz hlam
  exact hbase.inv hne

/-- Each resolvent term `s ↦ (s + λ)⁻¹` is holomorphic on `Ω` when `λ ≥ 0`. -/
theorem resolvent_term_holo_on_Omega (lam : ℝ) (hlam : 0 ≤ lam) :
    HolomorphicOnC (fun s => (s + (lam : ℂ))⁻¹) Ω :=
  fun z hz => (resolvent_term_analyticAt lam hlam hz).analyticWithinAt

/-- Brick 2b: resolvent sum differentiable on any ball `⊆ Ω`. -/
theorem Fstage_differentiableOn_ball
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 ≤ lam n)
    (c : ℂ) (r : ℝ) (hball : Metric.ball c r ⊆ Ω)
    (u : ℕ → ℝ) (hu : Summable u)
    (hbd : ∀ n, ∀ s ∈ Metric.ball c r, ‖(s + (lam n : ℂ))⁻¹‖ ≤ u n) :
    DifferentiableOn ℂ (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) (Metric.ball c r) := by
  refine differentiableOn_tsum_of_summable_norm hu ?_ Metric.isOpen_ball hbd
  intro n z hz
  have hzΩ : z ∈ Ω := hball hz
  exact (resolvent_term_analyticAt (lam n) (hlam n) hzΩ).differentiableAt.differentiableWithinAt

/-- Brick 2c: resolvent-trace sum holomorphic on all of `Ω`, from the local
summable-bound input (Appendix-A Cor. A.TRACE, local form). -/
theorem Fstage_holo_on_Omega
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 ≤ lam n)
    (hlocal : ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ Ω ∧
        ∃ u : ℕ → ℝ, Summable u ∧
          ∀ n, ∀ s ∈ Metric.ball z r, ‖(s + (lam n : ℂ))⁻¹‖ ≤ u n) :
    HolomorphicOnC (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) Ω := by
  intro z hz
  obtain ⟨r, hr, hball, u, hu, hbd⟩ := hlocal z hz
  have hdiff : DifferentiableOn ℂ (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) (Metric.ball z r) :=
    Fstage_differentiableOn_ball lam hlam z r hball u hu hbd
  -- differentiable on the open ball ⇒ analytic AT the center (full-space), then within Ω
  have hzc : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hAt : AnalyticAt ℂ (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) z := by
    have hballnhds : Metric.ball z r ∈ nhds z := Metric.isOpen_ball.mem_nhds hzc
    have hd2 : DifferentiableOn ℂ (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) (Metric.ball z r) := hdiff
    exact (hd2.analyticOn Metric.isOpen_ball).analyticAt hballnhds
  exact hAt.analyticWithinAt

#print axioms add_real_ne_zero_of_mem_Omega
#print axioms resolvent_term_holo_on_Omega
#print axioms Fstage_differentiableOn_ball
#print axioms Fstage_holo_on_Omega
