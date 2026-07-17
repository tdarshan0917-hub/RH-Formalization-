import Mathlib

/-!
# Holomorphic Montel — Node 1: uniform Lipschitz ⟹ equicontinuous (pure topology)

The load-bearing topological step of Montel: a family of functions `F i` that share a
single Lipschitz constant `C` is uniformly equicontinuous. No holomorphy here. Node 2
supplies the uniform Lipschitz constant for a locally-bounded holomorphic family via
the Cauchy estimate.

Part of discharging `HolomorphicMontelConvergence` (D.CAN-REM's last gap, p178).
-/

namespace RHFormalization
open Filter Topology Metric

/-- **Montel node 1 (topology).** A family with a common Lipschitz constant is uniformly
equicontinuous. -/
theorem uniformEquicontinuous_of_lipschitzWith
    {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (C : NNReal) (F : ι → X → Y) (hF : ∀ i, LipschitzWith C (F i)) :
    UniformEquicontinuous F := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  refine ⟨ε / (C + 1), by positivity, ?_⟩
  intro x y hxy i
  have hlip : dist (F i x) (F i y) ≤ C * dist x y := by
    have := (hF i).dist_le_mul x y
    simpa using this
  calc dist (F i x) (F i y) ≤ C * dist x y := hlip
    _ ≤ C * (ε / (C + 1)) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hxy) (by positivity)
    _ < ε := by
        have hCpos : (0:ℝ) < (C:ℝ) + 1 := by positivity
        have hfrac : (C:ℝ) / (C + 1) < 1 := by rw [div_lt_one hCpos]; linarith
        calc (C:ℝ) * (ε / (C + 1)) = ε * ((C:ℝ) / (C + 1)) := by ring
          _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
          _ = ε := mul_one ε

#print axioms uniformEquicontinuous_of_lipschitzWith

end RHFormalization
