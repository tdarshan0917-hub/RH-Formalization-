import RHFormalization.MontelCauchyDeriv
import Mathlib

/-!
# Holomorphic Montel — Node 1b-full: locally-bounded holomorphic ⟹ uniform Lipschitz on a ball

Composes the banked Cauchy estimate (`norm_deriv_le_of_sphere_bound`) with Mathlib's
mean-value Lipschitz bound. Holomorphic family bounded by `M` on `B̄(z₀, ρ+r) ⊆ U`
⟹ each `f i` is `(M/r)`-Lipschitz on `B(z₀, ρ)`, SAME constant for all `i`. Feeds
`uniformEquicontinuous_of_lipschitzWith` (node 1).

Part of discharging `HolomorphicMontelConvergence` (D.CAN-REM's last gap, p178).
-/

namespace RHFormalization
open Complex Metric

/-- **Montel node 1b-full.** A family holomorphic on `U`, bounded by `M` on
`closedBall z₀ (ρ + r) ⊆ U`, is uniformly `(M/r)`-Lipschitz on `ball z₀ ρ`. -/
theorem lipschitzOnWith_ball_of_bounded_holo
    {ι : Type*} (f : ι → ℂ → ℂ) {U : Set ℂ} {z₀ : ℂ} {ρ r M : ℝ}
    (hU : IsOpen U) (hr : 0 < r) (hM0 : 0 ≤ M)
    (hball : closedBall z₀ (ρ + r) ⊆ U)
    (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hbd : ∀ i, ∀ w ∈ closedBall z₀ (ρ + r), ‖f i w‖ ≤ M) :
    ∀ i, LipschitzOnWith (Real.toNNReal (M / r)) (f i) (ball z₀ ρ) := by
  intro i
  have hderiv : ∀ w ∈ ball z₀ ρ, ‖deriv (f i) w‖ ≤ M / r := by
    intro w hw
    have hdwz : dist w z₀ < ρ := mem_ball.mp hw
    have hwsub : closedBall w r ⊆ closedBall z₀ (ρ + r) :=
      closedBall_subset_closedBall' (by linarith)
    have hwU : closedBall w r ⊆ U := hwsub.trans hball
    have hsph : ∀ y ∈ sphere w r, ‖f i y‖ ≤ M := fun y hy =>
      hbd i y (hwsub (sphere_subset_closedBall hy))
    exact norm_deriv_le_of_sphere_bound hU (hf i) hr hwU hsph
  refine (convex_ball z₀ ρ).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
  · intro x hx
    have hxU : x ∈ U :=
      hball ((ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith))) hx)
    exact (hf i).differentiableAt (hU.mem_nhds hxU)
  · intro x hx
    -- ‖deriv‖₊ ≤ (M/r).toNNReal : reduce to the real inequality
    have hMr : (0:ℝ) ≤ M / r := by positivity
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hMr]
    exact hderiv x hx

#print axioms lipschitzOnWith_ball_of_bounded_holo

end RHFormalization
