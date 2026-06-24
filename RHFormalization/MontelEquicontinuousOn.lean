import RHFormalization.MontelUniformLipschitz
import RHFormalization.MontelEquicontinuous
import Mathlib

/-!
# Holomorphic Montel — equicontinuity composition: locally-bounded holo ⟹ equicontinuous on a ball

Chains node 1b-full (`lipschitzOnWith_ball_of_bounded_holo`, uniform Lipschitz constant on
`ball z₀ ρ`) into the set-restricted equicontinuity form. Result: a locally-bounded
holomorphic family is uniformly equicontinuous on `ball z₀ ρ` — the equicontinuity input
Ascoli (node 2) needs.

Part of discharging `HolomorphicMontelConvergence` (D.CAN-REM's last gap, p178).
-/

namespace RHFormalization
open Complex Metric

/-- **Equicontinuity of a locally-bounded holomorphic family on a ball.** -/
theorem uniformEquicontinuousOn_ball_of_bounded_holo
    {ι : Type*} (f : ι → ℂ → ℂ) {U : Set ℂ} {z₀ : ℂ} {ρ r M : ℝ}
    (hU : IsOpen U) (hr : 0 < r) (hM0 : 0 ≤ M)
    (hball : closedBall z₀ (ρ + r) ⊆ U)
    (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hbd : ∀ i, ∀ w ∈ closedBall z₀ (ρ + r), ‖f i w‖ ≤ M) :
    UniformEquicontinuousOn f (ball z₀ ρ) := by
  have hlip := lipschitzOnWith_ball_of_bounded_holo f hU hr hM0 hball hf hbd
  rw [← uniformEquicontinuous_restrict_iff]
  refine uniformEquicontinuous_of_lipschitzWith (Real.toNNReal (M / r)) _ ?_
  intro i
  exact lipschitzOnWith_iff_restrict.mp (hlip i)

#print axioms uniformEquicontinuousOn_ball_of_bounded_holo

end RHFormalization
