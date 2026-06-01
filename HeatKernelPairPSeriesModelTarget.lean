import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

noncomputable def heatKernelPairPSeriesModel_test :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    (1 / |(q.p : ℝ) + 1| ^ (2 : ℝ)) *
      (1 / |(q.m : ℝ) + 1| ^ (2 : ℝ))

theorem heatKernelPairPSeriesModel_test_summable :
    Summable heatKernelPairPSeriesModel_test := by
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
  simpa [heatKernelPairPSeriesModel_test, a, b,
    PrimePowerPair.p, PrimePowerPair.m] using hprod

end

end RHFormalization
