import RHFormalization.ArithmeticPrimeFStageBound
import RHFormalization.AppendixDSpikeSumExtraction

/-!
# ArithmeticPrimeBStageBound

This file proves the second fixed-stage estimate needed by

  ArithmeticPrimeDExport_of_F_B_bounds.

It bounds the finite witness B-stage by the finite sum of coefficient norms
times kernel norms.

This is still a fixed-stage finite-sum bound, not the final cutoff-limit theorem.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
Generic finite Nat-spike package norm bound.

This is just the triangle inequality plus `‖a*b‖ = ‖a‖‖b‖`.
-/
theorem finiteNatSpikePackage_norm_le_sum
    (I : Finset ℕ)
    (coeff : ℕ → ℂ)
    (K : ℕ → ℂ → ℂ)
    (s : ℂ) :
    ‖finiteNatSpikePackage I coeff K s‖ ≤
      I.sum (fun q => ‖coeff q‖ * ‖K q s‖) := by
  unfold finiteNatSpikePackage
  calc
    ‖I.sum (fun q => coeff q * K q s)‖
        ≤ I.sum (fun q => ‖coeff q * K q s‖) := by
          exact norm_sum_le _ _
    _ = I.sum (fun q => ‖coeff q‖ * ‖K q s‖) := by
          apply Finset.sum_congr rfl
          intro q hq
          simp [norm_mul]

/--
The stage-field witness B-stage is bounded by its finite termwise norm sum.
-/
theorem stageField_B_stage_norm_le_sum
    (α : DFiniteStage)
    (s : ℂ) :
    ‖stageFieldSpikeExtractionWitness.B_stage α s‖ ≤
      (stageFieldSpikeExtractionWitness.activeIndices α).sum
        (fun q =>
          ‖α.diagonalSpikeContribution q‖ *
          ‖stageFieldSpikeExtractionWitness.spikeKernel α q s‖) := by
  simpa [AppendixDFiniteSpikeExtractionWitness.B_stage] using
    finiteNatSpikePackage_norm_le_sum
      (stageFieldSpikeExtractionWitness.activeIndices α)
      α.diagonalSpikeContribution
      (stageFieldSpikeExtractionWitness.spikeKernel α)
      s

/--
If each finite spike term is bounded on `K` by `termBound q`, then the whole
B-stage is bounded by the finite sum of those bounds.
-/
theorem stageField_B_stage_bound_on_K_of_term_bounds
    (α : DFiniteStage)
    (Kset : Set ℂ)
    (termBound : ℕ → ℝ)
    (hterm :
      ∀ s ∈ Kset,
        ∀ q ∈ stageFieldSpikeExtractionWitness.activeIndices α,
          ‖α.diagonalSpikeContribution q‖ *
          ‖stageFieldSpikeExtractionWitness.spikeKernel α q s‖
            ≤ termBound q) :
    ∀ s ∈ Kset,
      ‖stageFieldSpikeExtractionWitness.B_stage α s‖ ≤
        (stageFieldSpikeExtractionWitness.activeIndices α).sum termBound := by
  intro s hs
  calc
    ‖stageFieldSpikeExtractionWitness.B_stage α s‖
        ≤ (stageFieldSpikeExtractionWitness.activeIndices α).sum
            (fun q =>
              ‖α.diagonalSpikeContribution q‖ *
              ‖stageFieldSpikeExtractionWitness.spikeKernel α q s‖) :=
          stageField_B_stage_norm_le_sum α s
    _ ≤ (stageFieldSpikeExtractionWitness.activeIndices α).sum termBound := by
          apply Finset.sum_le_sum
          intro q hq
          exact hterm s hs q hq

#print axioms finiteNatSpikePackage_norm_le_sum
#print axioms stageField_B_stage_norm_le_sum
#print axioms stageField_B_stage_bound_on_K_of_term_bounds

end

end RHFormalization
