import RHFormalization.CanonicalPrimePowerHeatKernelGaussianMajorant
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

Arithmetic summability target for the natValue majorant.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The arithmetic majorant produced by the log-Gaussian tail estimate.
-/
noncomputable def heatKernelNatValueMajorant :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹

/--
Comparison principle for the natValue majorant.
-/
theorem heatKernelNatValueMajorant_summable_of_model
    (model : PrimePowerPair → ℝ)
    (h_model_summable : Summable model)
    (h_le_model :
      ∀ q : PrimePowerPair,
        heatKernelNatValueMajorant q ≤ model q) :
    Summable heatKernelNatValueMajorant := by
  refine
    Summable.of_nonneg_of_le
      ?h_nonneg
      h_le_model
      h_model_summable
  intro q
  unfold heatKernelNatValueMajorant
  exact
    mul_nonneg
      (norm_nonneg q.weightC)
      (by positivity)


/--
Invalid prime-power pairs contribute zero to the natValue majorant.
-/
theorem heatKernelNatValueMajorant_eq_zero_of_not_isPrimePowerPair
    (q : PrimePowerPair)
    (hq : ¬ IsPrimePowerPair q) :
    heatKernelNatValueMajorant q = 0 := by
  unfold heatKernelNatValueMajorant
  simp [PrimePowerPair.weightC, PrimePowerPair.weightReal, hq]

/--
On valid prime-power pairs, the natValue majorant has the explicit real formula.
-/
theorem heatKernelNatValueMajorant_eq_valid_primePower_formula
    (q : PrimePowerPair)
    (hq : IsPrimePowerPair q) :
    heatKernelNatValueMajorant q =
      |Real.log (q.p : ℝ) / Real.sqrt (q.natValue : ℝ)| *
        ((q.natValue : ℝ) ^ 3)⁻¹ := by
  unfold heatKernelNatValueMajorant
  rw [norm_weightC_eq_abs_weightReal]
  simp [PrimePowerPair.weightReal, hq]



/--
A simple summable product p-series model on `PrimePowerPair = ℕ × ℕ`.
-/
noncomputable def heatKernelPairPSeriesModel :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    (1 / |(q.p : ℝ) + 1| ^ (2 : ℝ)) *
      (1 / |(q.m : ℝ) + 1| ^ (2 : ℝ))

/--
The product p-series model is summable.

This uses `summable_prod_of_nonneg`, which is available in this Mathlib checkout.
-/
theorem heatKernelPairPSeriesModel_summable :
    Summable heatKernelPairPSeriesModel := by
  let a : ℕ → ℝ := fun p : ℕ =>
    1 / |(p : ℝ) + 1| ^ (2 : ℝ)
  let b : ℕ → ℝ := fun m : ℕ =>
    1 / |(m : ℝ) + 1| ^ (2 : ℝ)

  have ha : Summable a := by
    simpa [a] using
      ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))

  have hb : Summable b := by
    simpa [b] using
      ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))

  have hf_nonneg :
      0 ≤ (fun x : ℕ × ℕ => a x.1 * b x.2) := by
    intro x
    dsimp [a, b]
    positivity

  have h_inner :
      ∀ p : ℕ, Summable fun m : ℕ => a p * b m := by
    intro p
    exact hb.mul_left (a p)

  have h_tsum :
      (fun p : ℕ => ∑' m : ℕ, a p * b m) =
        fun p : ℕ => a p * (∑' m : ℕ, b m) := by
    funext p
    simpa using
      (tsum_mul_left :
        (∑' m : ℕ, a p * b m) =
          a p * (∑' m : ℕ, b m))

  have h_outer :
      Summable fun p : ℕ => ∑' m : ℕ, a p * b m := by
    have houter' :
        Summable fun p : ℕ => (∑' m : ℕ, b m) * a p :=
      ha.mul_left (∑' m : ℕ, b m)
    have houter'' :
        Summable fun p : ℕ => a p * (∑' m : ℕ, b m) := by
      simpa [mul_comm] using houter'
    simpa [h_tsum] using houter''

  have hprod :
      Summable (fun x : ℕ × ℕ => a x.1 * b x.2) :=
    (summable_prod_of_nonneg hf_nonneg).2 ⟨h_inner, h_outer⟩

  change Summable (fun q : PrimePowerPair => a q.p * b q.m)
  simpa [heatKernelPairPSeriesModel, a, b,
    PrimePowerPair.p, PrimePowerPair.m] using hprod

/--
The current live theorem: the natValue majorant is summable.

This still contains `sorry`; the next real proof step is replacing this `sorry`.
-/
theorem heatKernelNatValueMajorant_summable :
    Summable heatKernelNatValueMajorant := by
  unfold heatKernelNatValueMajorant
  -- Current target:
  --   Summable
  --     (fun q : PrimePowerPair =>
  --       ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹)
  sorry

end

end RHFormalization
