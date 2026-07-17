import RHFormalization.ResolventTraceHolo
import RHFormalization.ResolventLocalBound
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# RHFormalization.ResolventStageConvergence

Convergence bridge: the finite partial sums of the resolvent trace
`F_N(s) = ∑_{i<N} 1/(s+λᵢ)` converge uniformly on a ball `⊆ Ω` to the full
sum `F(s) = ∑' i, 1/(s+λᵢ)`, given a summable per-term bound on that ball.

This is the finite-stage → limit passage (paper's R→∞ at the trace level),
expressed via Mathlib's `tendstoUniformlyOn_tsum_nat`.  Feeds Brick 1
(`FH_holo_from_locally_uniform_stages`).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- Partial sums of the resolvent trace converge uniformly on `ball c r ⊆ Ω`
to the full tsum, given a summable per-term bound on the ball. -/
theorem resolvent_partialSums_tendstoUniformlyOn_ball
    (lam : ℕ → ℝ)
    (c : ℂ) (r : ℝ)
    (u : ℕ → ℝ) (hu : Summable u)
    (hbd : ∀ n, ∀ s ∈ Metric.ball c r, ‖(s + (lam n : ℂ))⁻¹‖ ≤ u n) :
    TendstoUniformlyOn
      (fun (N : ℕ) (s : ℂ) => ∑ i ∈ Finset.range N, (s + (lam i : ℂ))⁻¹)
      (fun s => ∑' i, (s + (lam i : ℂ))⁻¹)
      atTop (Metric.ball c r) := by
  exact tendstoUniformlyOn_tsum_nat hu hbd

/-- Locally-uniform form on the ball (what Brick-1-style lemmas consume). -/
theorem resolvent_partialSums_tendstoLocallyUniformlyOn_ball
    (lam : ℕ → ℝ)
    (c : ℂ) (r : ℝ)
    (u : ℕ → ℝ) (hu : Summable u)
    (hbd : ∀ n, ∀ s ∈ Metric.ball c r, ‖(s + (lam n : ℂ))⁻¹‖ ≤ u n) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (s : ℂ) => ∑ i ∈ Finset.range N, (s + (lam i : ℂ))⁻¹)
      (fun s => ∑' i, (s + (lam i : ℂ))⁻¹)
      atTop (Metric.ball c r) :=
  (resolvent_partialSums_tendstoUniformlyOn_ball lam c r u hu hbd).tendstoLocallyUniformlyOn

#print axioms resolvent_partialSums_tendstoUniformlyOn_ball
#print axioms resolvent_partialSums_tendstoLocallyUniformlyOn_ball
